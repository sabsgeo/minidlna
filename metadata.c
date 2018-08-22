/* MiniDLNA media server
 * Copyright (C) 2008-2009  Justin Maggard
 *
 * This file is part of MiniDLNA.
 *
 * MiniDLNA is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License version 2 as
 * published by the Free Software Foundation.
 *
 * MiniDLNA is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with MiniDLNA. If not, see <http://www.gnu.org/licenses/>.
 */
#include "config.h"

#include <stdio.h>
#include <ctype.h>
#include <string.h>
#include <stdlib.h>
#include <libgen.h>
#include <unistd.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/param.h>
#include <fcntl.h>

#include <libexif/exif-loader.h>
#include <jpeglib.h>
#include <setjmp.h>
#include "libav.h"

#include "upnpglobalvars.h"
#include "tagutils/tagutils.h"
#include "image_utils.h"
#include "upnpreplyparse.h"
#include "tivo_utils.h"
#include "metadata.h"
#include "albumart.h"
#include "utils.h"
#include "sql.h"
#include "log.h"

#define FLAG_TITLE	0x00000001
#define FLAG_ARTIST	0x00000002
#define FLAG_ALBUM	0x00000004
#define FLAG_GENRE	0x00000008
#define FLAG_COMMENT	0x00000010
#define FLAG_CREATOR	0x00000020
#define FLAG_DATE	0x00000040
#define FLAG_DLNA_PN	0x00000080
#define FLAG_MIME	0x00000100
#define FLAG_DURATION	0x00000200
#define FLAG_RESOLUTION	0x00000400

/* Audio profile flags */
enum audio_profiles {
	PROFILE_AUDIO_UNKNOWN,
	PROFILE_AUDIO_MP3,
	PROFILE_AUDIO_AC3,
	PROFILE_AUDIO_WMA_BASE,
	PROFILE_AUDIO_WMA_FULL,
	PROFILE_AUDIO_WMA_PRO,
	PROFILE_AUDIO_MP2,
	PROFILE_AUDIO_PCM,
	PROFILE_AUDIO_AAC,
	PROFILE_AUDIO_AAC_MULT5,
	PROFILE_AUDIO_AMR
};

void getDateFromNFO(char *path, char *name, char *date)
{
	FILE *fptr;
	char buf1[20];
	char buf2[20];
	char *tok, *ptr;
	char nfo_file[MAXPATHLEN];
	char extFolder[11] = ".webviews2";
	
    time_t     timestamp;
    struct tm  ts;	
    
	memset(nfo_file, 0, MAXPATHLEN);
    
    strcpy(nfo_file, path);
    
    ptr = strrchr(nfo_file, '/');
    *ptr = '\0';
    strcat(nfo_file, "/");
    strcat(nfo_file, extFolder);
    strcat(nfo_file, "/.");
    strcat(nfo_file, name);
    strcat(nfo_file, ".NFO");

	fptr = fopen(nfo_file, "r");
	if(fptr == NULL)
	{
		date[0] = '\0';
		return;
	}

	fgets(buf1, 20, fptr);

	if(buf1 == NULL)
	{
		date[0] = '\0';
		return;			
	}	
	
	tok = strtok(buf1, "=");
	tok = strtok(NULL, "=");
	
	if(tok == NULL)
	{
		date[0] = '\0';
		return;			
	}
	
	timestamp = atoi(tok);
	
	if(timestamp == 0)
	{
		date[0] = '\0';
		return;	
	}
	
	ts = *localtime(&timestamp);
	
	strftime(buf2, sizeof(buf1), "%Y-%m-%d %H:%M:%S", &ts);
    printf("%s\n", buf2);
    
    strcpy(date, buf2);		
	
	fclose(fptr);
}

/* This function shamelessly copied from libdlna */
#define MPEG_TS_SYNC_CODE 0x47
#define MPEG_TS_PACKET_LENGTH 188
#define MPEG_TS_PACKET_LENGTH_DLNA 192 /* prepends 4 bytes to TS packet */
int
dlna_timestamp_is_present(const char *filename, int *raw_packet_size)
{
	unsigned char buffer[3*MPEG_TS_PACKET_LENGTH_DLNA];
	int fd, i;

	/* read file header */
	fd = open(filename, O_RDONLY);
	if( fd < 0 )
		return 0;
	i = read(fd, buffer, MPEG_TS_PACKET_LENGTH_DLNA*3);
	close(fd);
	if( i < 0 )
		return 0;
	for( i = 0; i < MPEG_TS_PACKET_LENGTH_DLNA; i++ )
	{
		if( buffer[i] == MPEG_TS_SYNC_CODE )
		{
			if (buffer[i + MPEG_TS_PACKET_LENGTH_DLNA] == MPEG_TS_SYNC_CODE &&
			    buffer[i + MPEG_TS_PACKET_LENGTH_DLNA*2] == MPEG_TS_SYNC_CODE)
			{
			        *raw_packet_size = MPEG_TS_PACKET_LENGTH_DLNA;
				if (buffer[i+MPEG_TS_PACKET_LENGTH] == 0x00 &&
				    buffer[i+MPEG_TS_PACKET_LENGTH+1] == 0x00 &&
				    buffer[i+MPEG_TS_PACKET_LENGTH+2] == 0x00 &&
				    buffer[i+MPEG_TS_PACKET_LENGTH+3] == 0x00)
					return 0;
				else
					return 1;
			} else if (buffer[i + MPEG_TS_PACKET_LENGTH] == MPEG_TS_SYNC_CODE &&
				   buffer[i + MPEG_TS_PACKET_LENGTH*2] == MPEG_TS_SYNC_CODE) {
			    *raw_packet_size = MPEG_TS_PACKET_LENGTH;
			    return 0;
			}
		}
	}
	*raw_packet_size = 0;
	return 0;
}

void
check_for_captions(const char *path, int64_t detailID)
{
	char file[MAXPATHLEN];
	char *p;
	int ret;

	strncpyt(file, path, sizeof(file));
	p = strip_ext(file);
	if (!p)
		p = strrchr(file, '\0');

	/* If we weren't given a detail ID, look for one. */
	if (!detailID)
	{
		detailID = sql_get_int64_field(db, "SELECT ID from DETAILS where (PATH > '%q.' and PATH <= '%q.z')"
		                            " and MIME glob 'video/*' limit 1", file, file);
		if (detailID <= 0)
		{
			//DPRINTF(E_MAXDEBUG, L_METADATA, "No file found for caption %s.\n", path);
			return;
		}
	}

	strcpy(p, ".srt");
	ret = access(file, R_OK);
	if (ret != 0)
	{
		strcpy(p, ".smi");
		ret = access(file, R_OK);
	}

	if (ret == 0)
	{
		sql_exec(db, "INSERT into CAPTIONS"
		             " (ID, PATH) "
		             "VALUES"
		             " (%lld, %Q)", detailID, file);
	}
}

void
parse_nfo(const char *path, metadata_t *m)
{
	FILE *nfo;
	char buf[65536];
	struct NameValueParserData xml;
	struct stat file;
	size_t nread;
	char *val, *val2;

	if( stat(path, &file) != 0 ||
	    file.st_size > 65536 )
	{
		DPRINTF(E_INFO, L_METADATA, "Not parsing very large .nfo file %s\n", path);
		return;
	}
	DPRINTF(E_DEBUG, L_METADATA, "Parsing .nfo file: %s\n", path);
	nfo = fopen(path, "r");
	if( !nfo )
		return;
	nread = fread(&buf, 1, sizeof(buf), nfo);
	
	ParseNameValue(buf, nread, &xml, 0);

	//printf("\ttype: %s\n", GetValueFromNameValueList(&xml, "rootElement"));
	val = GetValueFromNameValueList(&xml, "title");
	if( val )
	{
		char *esc_tag = unescape_tag(val, 1);
		val2 = GetValueFromNameValueList(&xml, "episodetitle");
		if( val2 ) {
			char *esc_tag2 = unescape_tag(val2, 1);
			xasprintf(&m->title, "%s - %s", esc_tag, esc_tag2);
			free(esc_tag2);
		} else {
			m->title = escape_tag(esc_tag, 1);
		}
		free(esc_tag);
	}

	val = GetValueFromNameValueList(&xml, "plot");
	if( val ) {
		char *esc_tag = unescape_tag(val, 1);
		m->comment = escape_tag(esc_tag, 1);
		free(esc_tag);
	}

	val = GetValueFromNameValueList(&xml, "capturedate");
	if( val ) {
		char *esc_tag = unescape_tag(val, 1);
		m->date = escape_tag(esc_tag, 1);
		free(esc_tag);
	}

	val = GetValueFromNameValueList(&xml, "genre");
	if( val )
	{
		free(m->genre);
		char *esc_tag = unescape_tag(val, 1);
		m->genre = escape_tag(esc_tag, 1);
		free(esc_tag);
	}

	val = GetValueFromNameValueList(&xml, "mime");
	if( val )
	{
		free(m->mime);
		char *esc_tag = unescape_tag(val, 1);
		m->mime = escape_tag(esc_tag, 1);
		free(esc_tag);
	}

	ClearNameValueList(&xml);
	fclose(nfo);
}

void
free_metadata(metadata_t *m, uint32_t flags)
{
	if( flags & FLAG_TITLE )
		free(m->title);
	if( flags & FLAG_ARTIST )
		free(m->artist);
	if( flags & FLAG_ALBUM )
		free(m->album);
	if( flags & FLAG_GENRE )
		free(m->genre);
	if( flags & FLAG_CREATOR )
		free(m->creator);
	if( flags & FLAG_DATE )
		free(m->date);
	if( flags & FLAG_COMMENT )
		free(m->comment);
	if( flags & FLAG_DLNA_PN )
		free(m->dlna_pn);
	if( flags & FLAG_MIME )
		free(m->mime);
	if( flags & FLAG_DURATION )
		free(m->duration);
	if( flags & FLAG_RESOLUTION )
		free(m->resolution);
}

int64_t
GetFolderMetadata(const char *name, const char *path, const char *artist, const char *genre, int64_t album_art)
{
	int ret;

	ret = sql_exec(db, "INSERT into DETAILS"
	                   " (TITLE, PATH, CREATOR, ARTIST, GENRE, ALBUM_ART) "
	                   "VALUES"
	                   " ('%q', %Q, %Q, %Q, %Q, %lld);",
	                   name, path, artist, artist, genre, album_art);
	if( ret != SQLITE_OK )
		ret = 0;
	else
		ret = sqlite3_last_insert_rowid(db);

	return ret;
}

int64_t
GetAudioMetadata(const char *path, char *name)
{
	char type[4];
	static char lang[6] = { '\0' };
	struct stat file;
	int64_t ret;
	char *esc_tag;
	int i;
	int64_t album_art = 0;
	struct song_metadata song;
	metadata_t m;
	uint32_t free_flags = FLAG_MIME|FLAG_DURATION|FLAG_DLNA_PN|FLAG_DATE;
	memset(&m, '\0', sizeof(metadata_t));

	if ( stat(path, &file) != 0 )
		return 0;
	strip_ext(name);

	if( ends_with(path, ".mp3") )
	{
		strcpy(type, "mp3");
		m.mime = strdup("audio/mpeg");
	}
	else if( ends_with(path, ".m4a") || ends_with(path, ".mp4") ||
	         ends_with(path, ".aac") || ends_with(path, ".m4p") )
	{
		strcpy(type, "aac");
		m.mime = strdup("audio/mp4");
	}
	else if( ends_with(path, ".3gp") )
	{
		strcpy(type, "aac");
		m.mime = strdup("audio/3gpp");
	}
	else if( ends_with(path, ".wma") || ends_with(path, ".asf") )
	{
		strcpy(type, "asf");
		m.mime = strdup("audio/x-ms-wma");
	}
	else if( ends_with(path, ".flac") || ends_with(path, ".fla") || ends_with(path, ".flc") )
	{
		strcpy(type, "flc");
		m.mime = strdup("audio/x-flac");
	}
	else if( ends_with(path, ".wav") )
	{
		strcpy(type, "wav");
		m.mime = strdup("audio/x-wav");
	}
	else if( ends_with(path, ".ogg") || ends_with(path, ".oga") )
	{
		strcpy(type, "ogg");
		m.mime = strdup("audio/ogg");
	}
	else if( ends_with(path, ".pcm") )
	{
		strcpy(type, "pcm");
		m.mime = strdup("audio/L16");
	}
	else
	{
		DPRINTF(E_WARN, L_METADATA, "Unhandled file extension on %s\n", path);
		return 0;
	}

	if( !(*lang) )
	{
		if( !getenv("LANG") )
			strcpy(lang, "en_US");
		else
			strncpyt(lang, getenv("LANG"), sizeof(lang));
	}

	if( readtags((char *)path, &song, &file, lang, type) != 0 )
	{
		DPRINTF(E_WARN, L_METADATA, "Cannot extract tags from %s!\n", path);
        	freetags(&song);
		free_metadata(&m, free_flags);
		return 0;
	}

	if( song.dlna_pn )
		m.dlna_pn = strdup(song.dlna_pn);
	if( song.year )
		xasprintf(&m.date, "%04d-01-01", song.year);
	xasprintf(&m.duration, "%d:%02d:%02d.%03d",
	                      (song.song_length/3600000),
	                      (song.song_length/60000%60),
	                      (song.song_length/1000%60),
	                      (song.song_length%1000));
	if( song.title && *song.title )
	{
		m.title = trim(song.title);
		if( (esc_tag = escape_tag(m.title, 0)) )
		{
			free_flags |= FLAG_TITLE;
			m.title = esc_tag;
		}
	}
	else
	{
		m.title = name;
	}
	for( i=ROLE_START; i<N_ROLE; i++ )
	{
		if( song.contributor[i] && *song.contributor[i] )
		{
			m.creator = trim(song.contributor[i]);
			if( strlen(m.creator) > 48 )
			{
				m.creator = strdup("Various Artists");
				free_flags |= FLAG_CREATOR;
			}
			else if( (esc_tag = escape_tag(m.creator, 0)) )
			{
				m.creator = esc_tag;
				free_flags |= FLAG_CREATOR;
			}
			m.artist = m.creator;
			break;
		}
	}
	/* If there is a band associated with the album, use it for virtual containers. */
	if( (i != ROLE_BAND) && (i != ROLE_ALBUMARTIST) )
	{
	        if( song.contributor[ROLE_BAND] && *song.contributor[ROLE_BAND] )
		{
			i = ROLE_BAND;
			m.artist = trim(song.contributor[i]);
			if( strlen(m.artist) > 48 )
			{
				m.artist = strdup("Various Artists");
				free_flags |= FLAG_ARTIST;
			}
			else if( (esc_tag = escape_tag(m.artist, 0)) )
			{
				m.artist = esc_tag;
				free_flags |= FLAG_ARTIST;
			}
		}
	}
	if( song.album && *song.album )
	{
		m.album = trim(song.album);
		if( (esc_tag = escape_tag(m.album, 0)) )
		{
			free_flags |= FLAG_ALBUM;
			m.album = esc_tag;
		}
	}
	if( song.genre && *song.genre )
	{
		m.genre = trim(song.genre);
		if( (esc_tag = escape_tag(m.genre, 0)) )
		{
			free_flags |= FLAG_GENRE;
			m.genre = esc_tag;
		}
	}
	if( song.comment && *song.comment )
	{
		m.comment = trim(song.comment);
		if( (esc_tag = escape_tag(m.comment, 0)) )
		{
			free_flags |= FLAG_COMMENT;
			m.comment = esc_tag;
		}
	}

	album_art = find_album_art(path, song.image, song.image_size);

	ret = sql_exec(db, "INSERT into DETAILS"
	                   " (PATH, SIZE, TIMESTAMP, DURATION, CHANNELS, BITRATE, SAMPLERATE, DATE,"
	                   "  TITLE, CREATOR, ARTIST, ALBUM, GENRE, COMMENT, DISC, TRACK, DLNA_PN, MIME, ALBUM_ART) "
	                   "VALUES"
	                   " (%Q, %lld, %lld, '%s', %d, %d, %d, %Q, %Q, %Q, %Q, %Q, %Q, %Q, %d, %d, %Q, '%s', %lld);",
	                   path, (long long)file.st_size, (long long)file.st_mtime, m.duration, song.channels, song.bitrate,
	                   song.samplerate, m.date, m.title, m.creator, m.artist, m.album, m.genre, m.comment, song.disc,
	                   song.track, m.dlna_pn, song.mime?song.mime:m.mime, album_art);
	if( ret != SQLITE_OK )
	{
		DPRINTF(E_ERROR, L_METADATA, "Error inserting details for '%s'!\n", path);
		ret = 0;
	}
	else
	{
		ret = sqlite3_last_insert_rowid(db);
	}
        freetags(&song);
	free_metadata(&m, free_flags);

	return ret;
}

/* For libjpeg error handling */
jmp_buf setjmp_buffer;
static void
libjpeg_error_handler(j_common_ptr cinfo)
{
	cinfo->err->output_message (cinfo);
	longjmp(setjmp_buffer, 1);
	return;
}

// returns -1 on failure
double parse_exif_coordinate(ExifEntry *e)
{
	ExifRational v_rat;
	signed char i;
	double coordinate = 0.0;
	unsigned char rational_size = exif_format_get_size(EXIF_FORMAT_RATIONAL);

	// coordinates are 3 rational components: degree, minute, second
	if (!e || e->components != 3 || e->format != EXIF_FORMAT_RATIONAL)
	{
		//DPRINTF(E_INFO, L_METADATA, "invalid coordinate entry with components: %lu format:%d\n", e ? e->components : 0, e ? e->format : 0);
		return -1;
	}
	ExifByteOrder byte_order    = exif_data_get_byte_order(e->parent->parent);

	for (i = 2; i >= 0; i--)
	{
		v_rat = exif_get_rational(e->data + i * rational_size, byte_order);
		//DPRINTF(E_INFO, L_METADATA, "coordinate rational %d: %d/%d\n", i, v_rat.numerator, v_rat.denominator);
		if (!v_rat.denominator)
		{
			//DPRINTF(E_INFO, L_METADATA, "invalid coordinate with 0 denominator: %d\n", i);
			return -1;
		}
		coordinate /= 60.0;
		coordinate += (double) v_rat.numerator / (double) v_rat.denominator;
	}

	return coordinate;
}

// sets latitude, longitude and altitude to 999999.0 if undefined
void extract_geolocation(ExifData *ed, double *latitude, double *longitude, double *altitude)
{
	// handy variable reused while parsing exif
	ExifEntry *e = NULL;
	ExifRational v_rat;
	ExifByte v_byte;
	char c;
	double coordinate;

	// exif byte order
	ExifByteOrder byte_order = exif_data_get_byte_order(ed);
	
	// default "undefined" values
	*latitude = *longitude = *altitude = 999999.0;

	// EXIF_TAG_GPS_ALTITUDE	RATIONAL	meters
	e = exif_content_get_entry(ed->ifd[EXIF_IFD_GPS], EXIF_TAG_GPS_ALTITUDE);
	if (e && e->components == 1 && e->format == EXIF_FORMAT_RATIONAL)
	{
		v_rat = exif_get_rational(e->data, byte_order);
		//DPRINTF(E_INFO, L_METADATA, "altitude rational: %d/%d\n", v_rat.numerator, v_rat.denominator);

		if (v_rat.denominator)
		{
			// EXIF_TAG_GPS_ALTITUDE_REF	BYTE		0: above sea level, 1: below sea level
			e = exif_content_get_entry(ed->ifd[EXIF_IFD_GPS], EXIF_TAG_GPS_ALTITUDE_REF);
			if (e && e->components == 1 && e->format == EXIF_FORMAT_BYTE)
			{
				v_byte = e->data[0];
				// DPRINTF(E_INFO, L_METADATA, "altitude ref byte: %d\n", v_byte);

				// 0 and 1 are the only valid values
				if (v_byte == 0 || v_byte == 1)
				{
					*altitude = (double) v_rat.numerator / (double) v_rat.denominator;

					// 1 means below sea level
					if (v_byte == 1)
						*altitude = -*altitude;

					//DPRINTF(E_INFO, L_METADATA, "altitude double: %f\n", *altitude);
				}
				else
				{
					//DPRINTF(E_INFO, L_METADATA, "invalid altitude ref value: %d\n", v_byte);
				}
			}
			else
			{
				//DPRINTF(E_INFO, L_METADATA, "invalid altitude ref with components: %lu format: %d\n", e ? e->components : 0, e ? e->format : 0);
			}
		}
		else
		{
			//DPRINTF(E_INFO, L_METADATA, "invalid altitude rational with 0 denominator\n");
		}
	}
	else
	{
		//DPRINTF(E_INFO, L_METADATA, "invalid altitude with components: %lu format: %d\n", e ? e->components: 0, e ? e->format : 0);
	}

	// TODO: could share some parsing code between latitude and longitude

	// EXIF_TAG_GPS_LATITUDE_REF    ASCII		N or S
	e = exif_content_get_entry(ed->ifd[EXIF_IFD_GPS], EXIF_TAG_GPS_LATITUDE_REF);
	// I have seen 2 components of size 2, so I am not too picky
	if (e /* && e->components == 1 */ && e->format == EXIF_FORMAT_ASCII && e->size >= 1)
	{
		c = e->data[0];
		//DPRINTF(E_INFO, L_METADATA, "latitude ref ascii: %c\n", c);

		// N and S are the only 2 valid values
		if (c == 'N' || c == 'S')
		{
			// EXIF_TAG_GPS_LATITUDE 			expressed as three RATIONAL values giving the degrees, minutes, and seconds, respectively. When degrees, minutes and seconds are expressed, the format is dd/1,mm/1,ss/1. When degrees and minutes are used and, for example, fractions of minutes are given up to two decimal places, the format is dd/1,mmmm/100,0/1.
			e = exif_content_get_entry(ed->ifd[EXIF_IFD_GPS], EXIF_TAG_GPS_LATITUDE);
			coordinate = parse_exif_coordinate(e);

			//DPRINTF(E_INFO, L_METADATA, "pre-ref latitude double: %f\n", coordinate);

			// latitudes are between 0 and 90 degrees
			if (coordinate >= 0.0 && coordinate <= 90.0)
			{
				*latitude = coordinate;

				// South latitudes are negative
				if (c == 'S')
					*latitude = -*latitude;

				//DPRINTF(E_INFO, L_METADATA, "latitude double: %f\n", *latitude);
			}
			else
			{
				//DPRINTF(E_INFO, L_METADATA, "invalid latitude value: %f\n", coordinate);
			}
		}
		else
		{
			//DPRINTF(E_INFO, L_METADATA, "invalid latitude ref value: %c\n", c);
		}
	}
	else
	{
		//DPRINTF(E_INFO, L_METADATA, "invalid latitude ref enty with components: %lu, format: %d\n", e ? e->components : 0, e ? e->format : 0);
	}

	// EXIF_TAG_GPS_LONGITUDE_REF   ASCII		E or W
	e = exif_content_get_entry(ed->ifd[EXIF_IFD_GPS], EXIF_TAG_GPS_LONGITUDE_REF);
	// I have seen 2 components of size 2, so I am not too picky
	if (e /* && e->components == 1 */ && e->format == EXIF_FORMAT_ASCII && e->size >= 1)
	{
		c = e->data[0];
		//DPRINTF(E_INFO, L_METADATA, "longitude ref ascii: %c\n", c);

		// W and E are the only 2 valid values
		if (c == 'W' || c == 'E')
		{
			// EXIF_TAG_GPS_LONGITUDE			expressed as three RATIONAL values giving the degrees, minutes, and seconds, respectively. When degrees, minutes and seconds are expressed, the format is dd/1,mm/1,ss/1. When degrees and minutes are used and, for example, fractions of minutes are given up to two decimal places, the format is dd/1,mmmm/100,0/1.
			e = exif_content_get_entry(ed->ifd[EXIF_IFD_GPS], EXIF_TAG_GPS_LONGITUDE);
			coordinate = parse_exif_coordinate(e);

			//DPRINTF(E_INFO, L_METADATA, "pre-ref longitude double: %f\n", coordinate);

			// longitudes are between 0 and 180 degrees
			if (coordinate >= 0.0 && coordinate <= 180.0)
			{
				*longitude = coordinate;

				// West longitudes are negative
				if (c == 'W')
					*longitude = -*longitude;

				//DPRINTF(E_INFO, L_METADATA, "longitude double: %f\n", *longitude);
			}
			else
			{
				//DPRINTF(E_INFO, L_METADATA, "invalid longitude value: %f\n", coordinate);
			}
		}
		else
		{
			//DPRINTF(E_INFO, L_METADATA, "invalid longitude ref value: %c\n", c);
		}
	}
	else
	{
		//DPRINTF(E_INFO, L_METADATA, "invalid longitude ref enty with components: %lu, format: %d\n", e ? e->components : 0, e ? e->format : 0);
	}
}

int64_t
GetJpegImageMetadata(const char *path, char *name)
{
	ExifData *ed;
	ExifEntry *e = NULL;
	ExifLoader *l;
	struct jpeg_decompress_struct cinfo;
	struct jpeg_error_mgr jerr;
	FILE *infile;
	int width=0, height=0, thumb=0;
	char latitude[14]  = "NULL";
	char longitude[14] = "NULL";
	char altitude[14]  = "NULL";
	char make[32], model[64] = {'\0'};
	char b[1024];
	char file_name[MAXPATHLEN];
	struct stat file;
	int64_t ret;
	image_s *imsrc;
	metadata_t m;
	uint32_t free_flags = 0xFFFFFFFF;
	memset(&m, '\0', sizeof(metadata_t));
	
	strcpy(file_name, name);
	
	//DEBUG DPRINTF(E_DEBUG, L_METADATA, "Parsing %s...\n", path);
	if ( stat(path, &file) != 0 )
		return 0;
	strip_ext(name);
	//DEBUG DPRINTF(E_DEBUG, L_METADATA, " * size: %jd\n", file.st_size);

	/* MIME hard-coded to JPEG for now, until we add PNG support */
	m.mime = strdup("image/jpeg");

	l = exif_loader_new();
	exif_loader_write_file(l, path);
	ed = exif_loader_get_data(l);
	exif_loader_unref(l);
	if( !ed )
		goto no_exifdata;

	e = exif_content_get_entry (ed->ifd[EXIF_IFD_EXIF], EXIF_TAG_DATE_TIME_ORIGINAL);
	if( e || (e = exif_content_get_entry(ed->ifd[EXIF_IFD_EXIF], EXIF_TAG_DATE_TIME_DIGITIZED)) )
	{
		m.date = strdup(exif_entry_get_value(e, b, sizeof(b)));
		if( strlen(m.date) > 10 )
		{
			m.date[4] = '-';
			m.date[7] = '-';
			m.date[10] = 'T';
		}
		else {
			free(m.date);
			m.date = NULL;
		}
	}
	else {
		image_get_jpeg_date_xmp(path, &m.date);
	}
	
	if(m.date == NULL)
	{
		char date[20];
		getDateFromNFO(path, file_name, date);
		if(date[0] == '\0')
		{
			free(m.date);
			m.date = NULL;		
		}
		else
		{
			m.date = strdup(date);
			m.date[10] = 'T';
		}
	}
	
	//DEBUG DPRINTF(E_DEBUG, L_METADATA, " * date: %s\n", m.date);

	e = exif_content_get_entry(ed->ifd[EXIF_IFD_0], EXIF_TAG_MAKE);
	if( e )
	{
		strncpyt(make, exif_entry_get_value(e, b, sizeof(b)), sizeof(make));
		e = exif_content_get_entry(ed->ifd[EXIF_IFD_0], EXIF_TAG_MODEL);
		if( e )
		{
			strncpyt(model, exif_entry_get_value(e, b, sizeof(b)), sizeof(model));
			if( !strcasestr(model, make) )
				snprintf(model, sizeof(model), "%s %s", make, exif_entry_get_value(e, b, sizeof(b)));
			m.creator = escape_tag(trim(model), 1);
		}
	}
	//DEBUG DPRINTF(E_DEBUG, L_METADATA, " * model: %s\n", model);

	m.rotation = 0;//kwilt
//No orientation and thumbnail extraction needed - kwilt
#if 0
	e = exif_content_get_entry(ed->ifd[EXIF_IFD_0], EXIF_TAG_ORIENTATION);
	if( e )
	{
		switch( exif_get_short(e->data, exif_data_get_byte_order(ed)) )
		{
		case 3:
			m.rotation = 180;
			break;
		case 6:
			m.rotation = 90;
			break;
		case 8:
			m.rotation = 270;
			break;
		default:
			m.rotation = 0;
			break;
		}
	}

	if( ed->size )
	{
		/* We might need to verify that the thumbnail is 160x160 or smaller */
		if( ed->size > 12000 )
		{
			imsrc = image_new_from_jpeg(NULL, 0, ed->data, ed->size, 1, ROTATE_NONE);
			if( imsrc )
			{
 				if( (imsrc->width <= 160) && (imsrc->height <= 160) )
					thumb = 1;
				image_free(imsrc);
			}
		}
		else
			thumb = 1;
	}
#endif //Kwilt
	//DEBUG DPRINTF(E_DEBUG, L_METADATA, " * thumbnail: %d\n", thumb);

	double lat, lon, alt;
	extract_geolocation(ed, &lat, &lon, &alt);
	if (lat != 999999.0) sprintf(latitude,  "%.8f", lat);
	if (lon != 999999.0) sprintf(longitude, "%.8f", lon);
	if (alt != 999999.0) sprintf(altitude,  "%.8f", alt);

	exif_data_unref(ed);

no_exifdata:
	/* If SOF parsing fails, then fall through to reading the JPEG data with libjpeg to get the resolution */
	if( image_get_jpeg_resolution(path, &width, &height) != 0 || !width || !height )
	{
		infile = fopen(path, "r");
		if( infile )
		{
			cinfo.err = jpeg_std_error(&jerr);
			jerr.error_exit = libjpeg_error_handler;
			jpeg_create_decompress(&cinfo);
			if( setjmp(setjmp_buffer) )
				goto error;
			jpeg_stdio_src(&cinfo, infile);
			jpeg_read_header(&cinfo, TRUE);
			jpeg_start_decompress(&cinfo);
			width = cinfo.output_width;
			height = cinfo.output_height;
			error:
			jpeg_destroy_decompress(&cinfo);
			fclose(infile);
		}
	}
	//DEBUG DPRINTF(E_DEBUG, L_METADATA, " * resolution: %dx%d\n", width, height);

	if( !width || !height )
	{
		free_metadata(&m, free_flags);
		return 0;
	}
m.dlna_pn=NULL;//Kwilt
/* No dlna_pn needed - Kwilt
	if( width <= 640 && height <= 480 )
		m.dlna_pn = strdup("JPEG_SM");
	else if( width <= 1024 && height <= 768 )
		m.dlna_pn = strdup("JPEG_MED");
	else if( (width <= 4096 && height <= 4096) || !GETFLAG(DLNA_STRICT_MASK) )
		m.dlna_pn = strdup("JPEG_LRG");
*/
	xasprintf(&m.resolution, "%dx%d", width, height);

	ret = sql_exec(db, "INSERT into DETAILS"
	                   " (PATH, TITLE, SIZE, TIMESTAMP, DATE, RESOLUTION,"
	                    " ROTATION, THUMBNAIL, CREATOR, DLNA_PN, MIME, LATITUDE, LONGITUDE, ALTITUDE) "
	                   "VALUES"
	                   " (%Q, '%q', %lld, %lld, %Q, %Q, %u, %d, %Q, %Q, %Q, %s, %s, %s);",
	                   path, name, (long long)file.st_size, (long long)file.st_mtime, m.date,
	                   m.resolution, m.rotation, thumb, m.creator, m.dlna_pn, m.mime,
	                   latitude, longitude, altitude);
	if( ret != SQLITE_OK )
	{
		DPRINTF(E_ERROR, L_METADATA, "Error inserting details for '%s'!\n", path);
		ret = 0;
	}
	else
	{
		ret = sqlite3_last_insert_rowid(db);
	}
	free_metadata(&m, free_flags);

	return ret;
}

void parse_iso_6709(char *location, char *latitude, char *longitude, char *altitude)
{
	// Format: https://en.wikipedia.org/wiki/ISO_6709
	// Sample values:
	// Seen:     +37.4034-122.1201/
	// Seen:     +53.6372+002.0612+027.000/
	// Not Seen: +27.5916+086.5640+8850CRSWGS_84/
	// Not Seen: +90+000/
	// The CRS should be appended to the altitude, before the slash, but is not in practice
	// There are also formats like ddmm.xxx or ddmmss.xxx instead of dd.xxxx
	// I ignore CRS and it is WGS_84

	// begining of the latitude
	char *lat = location;

	// bail out if the latitude is empty or does not start with + or -
	if (*lat != '+' && *lat != '-' )
		return;

	if (location[strlen(location) -1] != '/')
		return;
	
	// begining of the longitude
	char *lon = lat + 1;
	
	// parse latitude to find the begining of the longitude, or the end of the string
	while (*lon != 0 && *lon != '+' && *lon != '-')
		lon++;

	// bail out if the begining of the longitude was not found
	if (!*lon)
		return;

	// begining of the altitude
	char *alt = lon + 1;

	// parse longitude to find the begining of the altitude, or the end of the string or slash
	while (*alt != 0 && *alt != '+' && *alt != '-' && *alt != '/')
		alt++;

	// bail out if the end of the longitude was not found
	if (!*alt)
		return;

	// end of altitude
	char *end = NULL;

	// if we did not reach the slash, then look for the end of the altitude
	if (*alt != '/')
	{
		end = alt + 1;

		// parse altitude to find the end of the altitude, or the end of the string or slash or C ("CRS")
		while (*end != 0 && *end != 'C' && *end != '/')
			end++;

		// if the altitude does not end with slash or C, ignore it
		if (!*end) 
			end = NULL;
	}

	char slat[14];
	char slon[14];
	char salt[14];
	memset(slat, 0, 14);
	memset(slon, 0, 14);
	memset(salt, 0, 14);
	strncpy(slat, lat, lon - lat);
	strncpy(slon, lon, alt - lon);
	// DPRINTF(E_WARN, L_METADATA, "lat: %s\n", slat);
	// DPRINTF(E_WARN, L_METADATA, "lon: %s\n", slon);
	if (end)
	{
		strncpy(salt, alt, end - alt);
		// DPRINTF(E_WARN, L_METADATA, "alt: %s\n", salt);
	}

	// make sure the format is ±DD.D for latitude and ±DDD.D for longitude
	// i.e. degrees and decimal degrees, not minutes or seconds
	// which are another format, that I haven't seen used in practice
	char *dot_index;
	dot_index = strchr(slat, '.');
	if ((dot_index ? dot_index - slat : strlen(slat)) != 3)
	{
		// DPRINTF(E_WARN, L_METADATA, "latitude format is not DD.D: %s\n", slat);
		return;
	}
	dot_index = strchr(slon, '.');
	if ((dot_index ? dot_index - slon : strlen(slon)) != 4)
	{
		// DPRINTF(E_WARN, L_METADATA, "longitude format is not DDD.D: %s\n", slon);
		return;
	}

	char *dend;
	double d;

	d = strtod(slat, &dend);
	if (!*dend && d >= -90.0 && d <= 90)
		sprintf(latitude,  "%.8f", d);

	d = strtod(slon, &dend);
	if (!*dend && d >= -180.0 && d <= 180)
		sprintf(longitude,  "%.8f", d);

	if (end)
	{
		d = strtod(salt, &dend);
		if (!*dend)
			sprintf(altitude,  "%.8f", d);
	}
}


#define BE32(b) (*(b)<<24) | (*((b)+1)<<16) | (*((b)+2)<<8) | *((b)+3)

static uint8_t *
_png_readchunk (FILE *file, size_t size)
{
	uint8_t *buf = malloc (size);

	if (buf == (uint8_t *)NULL)
		return NULL;

	if (fread (buf, 1, size, file) != size)
	{
		free (buf);
		return NULL;
	}
	/* seek past the checksum */
	if (fseek (file, 4, SEEK_CUR))
	{
		free (buf);
		return NULL;
	}
	return buf;
}

static int64_t
GetPngImageMetadata(const char *path, char *name)
{
	FILE *file;
	uint32_t width=0, height=0;
	int thumb=0;
	int got_header = 0;
	struct stat statbuf;
	int64_t ret;
	metadata_t m;
	memset(&m, '\0', sizeof(metadata_t));
	uint8_t tagbuf[8];
	uint32_t free_flags = 0xFFFFFFFF;
	char file_name[MAXPATHLEN];		
	
	strcpy(file_name, name);	

	if ( stat(path, &statbuf) != 0 )
		return 0;
	strip_ext(name);

	if ((file = fopen (path, "rb")) == (FILE *)NULL)
	{
		DPRINTF (E_ERROR, L_METADATA, "Error opening \"%s\": %s\n",
				path, strerror (errno));
		return 0;
	}

	if (fread (tagbuf, 1, 8, file) != 8)
	{
		fclose (file);
		return 0;
	}

	if (memcmp (tagbuf, "\x89PNG\x0d\x0a\x1a\x0a", 8))
	{
		DPRINTF (E_WARN, L_METADATA,
				"\"%s\" not a PNG file.\n", path);
		fclose (file);
		return 0;
	}

	/* Go through the chunks */

	// DPRINTF (E_WARN, L_METADATA, "-- %s\n", path);

	for (;;)
	{
		int32_t chunksize;
		char *chunkname[5];
		uint8_t *buf;

		if ((fread (tagbuf, 1, 8, file)) != 8)
		{
			DPRINTF (E_WARN, L_METADATA,
					"%s: Premature EOF.\n", path);
			fclose (file);
			free_metadata(&m, free_flags);
			return 0;
		}
		chunksize = BE32 (&tagbuf[0]);
		memcpy (chunkname, &tagbuf[4], 4);
		chunkname[4] = '\x00';

		// DPRINTF (E_WARN, L_METADATA, "tag %c%c%c%c\n", tagbuf[4], tagbuf[5], tagbuf[6], tagbuf[7]);

		// end or image contents
		if (!memcmp (&tagbuf[4], "IEND", 4) || !memcmp (&tagbuf[4], "IDAT", 4))
		{
			break;
		}
		else if (chunksize <= 0)
		{
			if (fseek (file, 4, SEEK_CUR))
			{
				DPRINTF (E_WARN, L_METADATA,
						"%s: Seek error.\n", path);
				fclose (file);
				free_metadata(&m, free_flags);
				return 0;
			}
			continue;
		}
		// width and height
		else if (!memcmp (&tagbuf[4], "IHDR", 4)) {
			if ((buf = _png_readchunk (file, chunksize)) == NULL)
			{
				fclose (file);
				free_metadata(&m, free_flags);
				return 0;
			}
			got_header = 1;

			/* width and height are 32-bit BE starting at offset 0 */
			width = BE32 (&buf[0]);
			height = BE32 (&buf[4]);
			free (buf);
			continue;
		}
		else if (!memcmp (&tagbuf[4], "tIME", 4))
		{
			if ((buf = _png_readchunk (file, chunksize)) == NULL)
			{
				fclose (file);
				free_metadata(&m, free_flags);
				return 0;
			}
			if (m.date)
				free (m.date);

			xasprintf (&m.date, "%04d-%02d-%02dT%02d:%02d:%02d",
					(int)(buf[0]<<8 | buf[1]),
					(int)buf[2], (int)buf[3],
					(int)buf[4], (int)buf[5], (int)buf[6]);		
			free (buf);
			continue;
		}
//		else if (!memcmp (&tagbuf[4], "tEXt", 4) || 
//				!memcmp (&tagbuf[4], "iTXt", 4))
//		{
//			int international = !memcmp (&tagbuf[4], "iTXt", 4),
//					remaining = chunksize;
//			char *keyword, *value;
//			uint8_t *textp;
//			int l;
//
//			if ((buf = _png_readchunk (file, chunksize)) == NULL)
//			{
//				fclose (file);
//				free_metadata(&m, free_flags);
//				return 0;
//			}
//
//			textp = buf;
//			keyword = (char *)buf;
//			l = strlen (keyword) + 1;
//			textp += l;
//			if ((remaining -= l) <= 0)
//				goto textdone;
//
//			if (international)
//			{
//				char *lang;
//
//				if (*textp)
//					/* compressed */
//					goto textdone;
//
//				textp += 2;
//				if ((remaining -= 2) <= 0)
//					goto textdone;
//
//				/* language */
//				lang = (char *)textp;
//				l = strlen (lang) + 1;
//				textp += l;
//				if ((remaining -= l) <= 0)
//					goto textdone;
//
//				/* translated keyword */
//				l = strlen ((char *)textp) + 1;
//				textp += l;
//				if ((remaining -= l) <= 0)
//					goto textdone;
//			}
//
//			/* whatever's left is the value */
//			if ((value = malloc (remaining + 1)) == (char *)NULL)
//			{
//				DPRINTF (E_ERROR, L_METADATA, "Allocation error.\n");
//				free (buf);
//				fclose (file);
//				free_metadata(&m, free_flags);
//				return 0;
//			}
//
//			memcpy (value, textp, remaining);
//			value[remaining] = '\0';
//
//			// DPRINTF(E_WARN, L_METADATA, "    %s	%s\n", keyword, value );
//
//			if (!strcmp (keyword, "Title"))
//			{
//				if (m.title)
//					free (m.title);
//				m.title = value;
//			}
//			else if (!strcmp (keyword, "Author"))
//			{
//				if (m.creator)
//					free (m.creator);
//				m.creator = value;
//			}
//			else
//			{
//				free (value);
//			}
//
//textdone:
//			free (buf);
//		}
		else
		{
			/* move on to the next chunk */
			if (fseek (file, chunksize+4, SEEK_CUR))
			{
				DPRINTF (E_WARN, L_METADATA,
						"%s: Seek error.\n", path);
				fclose (file);
				free_metadata(&m, free_flags);
				return 0;
			}
		}
	}
	
	if(m.date == NULL)
	{
		char date[20];
		getDateFromNFO(path, file_name, date);
		if(date[0] == '\0')
		{
			free(m.date);
			m.date = NULL;		
		}
		else
		{
			m.date = strdup(date);
			m.date[10] = 'T';
		}
	}

	fclose (file);

	if (!got_header)
	{
		DPRINTF (E_WARN, L_METADATA,
				"%s: No PNG header.\n", path);
		free_metadata (&m, free_flags);
		return 0;
	}

	xasprintf(&m.resolution, "%dx%d", (int)width, (int)height);
	m.rotation = 0;
	thumb = 0;
	m.dlna_pn = NULL;
	m.mime = strdup("image/png");

	if (!m.title)
		m.title = strdup (name);

	DPRINTF (E_MAXDEBUG, L_METADATA,
			"Processed \"%s\":\n  Name: %s\n  Resolution: %s\n",
			path, name, m.resolution);

	ret = sql_exec(db, "INSERT into DETAILS"
	                   " (PATH, TITLE, SIZE, TIMESTAMP, DATE, RESOLUTION,"
	                    " ROTATION, THUMBNAIL, CREATOR, DLNA_PN, MIME) "
	                   "VALUES"
	                   " (%Q, '%q', %lld, %lld, %Q, %Q, %u, %d, %Q, %Q, %Q);",
	                   path, m.title, (long long)statbuf.st_size,
					   (long long)statbuf.st_mtime, m.date, m.resolution,
					   m.rotation, thumb, m.creator, m.dlna_pn, m.mime);
	if( ret != SQLITE_OK )
	{
		DPRINTF(E_ERROR, L_METADATA, "Error inserting details for '%s'!\n", path);
		ret = 0;
	}
	else
	{
		ret = sqlite3_last_insert_rowid(db);
	}
	free_metadata(&m, FLAG_MIME | FLAG_RESOLUTION);

	return ret;
}

static int64_t
GetGifImageMetadata(const char *path, char *name)
{
	FILE *file;
	uint32_t width=0, height=0;
	int thumb=0;
	struct stat statbuf;
	int64_t ret;
	metadata_t m;
	memset(&m, '\0', sizeof(metadata_t));
	uint8_t tagbuf[10];

	if ( stat(path, &statbuf) != 0 )
		return 0;
	strip_ext(name);

	if ((file = fopen (path, "rb")) == (FILE *)NULL)
	{
		DPRINTF (E_ERROR, L_METADATA, "Error opening \"%s\": %s\n",
				path, strerror (errno));
		return 0;
	}

	if (fread (tagbuf, 1, 10, file) != 10)
	{
		fclose (file);
		return 0;
	}

	if (memcmp (tagbuf, "GIF", 3))
	{
		DPRINTF (E_WARN, L_METADATA,
				"\"%s\" not a GIF file.\n", path);
		fclose (file);
		return 0;
	}

	width  = tagbuf[6] + (tagbuf[7]<<8);
	height = tagbuf[8] + (tagbuf[9]<<8);

	fclose (file);

	xasprintf(&m.resolution, "%dx%d", (int)width, (int)height);
	m.rotation = 0;
	thumb = 0;
	m.mime = strdup("image/gif");

	if (!m.title)
		m.title = strdup (name);

	DPRINTF (E_MAXDEBUG, L_METADATA,
			"Processed \"%s\":\n  Name: %s\n  Resolution: %s\n",
			path, name, m.resolution);

	ret = sql_exec(db, "INSERT into DETAILS"
	                   " (PATH, TITLE, SIZE, TIMESTAMP, RESOLUTION,"
	                    " ROTATION, THUMBNAIL, MIME) "
	                   "VALUES"
	                   " (%Q, '%q', %lld, %lld, %Q, %u, %d, %Q);",
	                   path, m.title, (long long)statbuf.st_size,
					   (long long)statbuf.st_mtime, m.resolution,
					   m.rotation, thumb, m.mime);
	if( ret != SQLITE_OK )
	{
		DPRINTF(E_ERROR, L_METADATA, "Error inserting details for '%s'!\n", path);
		ret = 0;
	}
	else
	{
		ret = sqlite3_last_insert_rowid(db);
	}
	free_metadata(&m, FLAG_MIME | FLAG_RESOLUTION);

	return ret;
}

static int64_t
GetBmpImageMetadata(const char *path, char *name)
{
	FILE *file;
	int32_t width=0, height=0;
	int thumb=0;
	struct stat statbuf;
	int64_t ret;
	metadata_t m;
	memset(&m, '\0', sizeof(metadata_t));
	uint8_t tagbuf[26];
	int32_t header_size; 

	if ( stat(path, &statbuf) != 0 )
		return 0;
	strip_ext(name);


	if ((file = fopen (path, "rb")) == (FILE *)NULL)
	{
		DPRINTF (E_ERROR, L_METADATA, "Error opening \"%s\": %s\n",
				path, strerror (errno));
		return 0;
	}

	if (fread (tagbuf, 1, 26, file) != 26)
	{
		fclose (file);
		return 0;
	}

	if (memcmp (tagbuf, "BM", 2))
	{
		DPRINTF (E_WARN, L_METADATA,
				"\"%s\" is not a BMP file.\n", path);
		fclose (file);
		return 0;
	}

	fclose (file);

	header_size = tagbuf[14] | tagbuf[15]<<8 | tagbuf[16]<<16 | tagbuf[17]<<24; 
	if (header_size > 12)
	{
		// width and height are 4 byte signed, little endian 
		width  = tagbuf[18] | tagbuf[19]<<8 | tagbuf[20]<<16 | tagbuf[21]<<24; 
		height = tagbuf[22] | tagbuf[23]<<8 | tagbuf[24]<<16 | tagbuf[25]<<24; 
	}
	else if (header_size == 12)
	{
		// width and height are 2 byte signed, little endian 
		width  = tagbuf[18] | tagbuf[19]<<8; 
		height = tagbuf[20] | tagbuf[21]<<8; 
	}
	else
	{
		DPRINTF (E_WARN, L_METADATA, "\"%s\" does not have a valide BMP header size.\n", path);
		return 0;
	}

	// dimensions could be negative (flipped bitmap)
	width  = abs(width);
	height = abs(height);

	xasprintf(&m.resolution, "%dx%d", (int)width, (int)height);
	m.rotation = 0;
	thumb = 0;
	m.mime = strdup("image/bmp");

	if (!m.title)
		m.title = strdup (name);

	DPRINTF (E_MAXDEBUG, L_METADATA,
			"Processed \"%s\":\n  Name: %s\n  Resolution: %s\n",
			path, name, m.resolution);

	ret = sql_exec(db, "INSERT into DETAILS"
	                   " (PATH, TITLE, SIZE, TIMESTAMP, RESOLUTION,"
	                    " ROTATION, THUMBNAIL, MIME) "
	                   "VALUES"
	                   " (%Q, '%q', %lld, %lld, %Q, %u, %d, %Q);",
	                   path, m.title, (long long)statbuf.st_size,
					   (long long)statbuf.st_mtime, m.resolution,
					   m.rotation, thumb, m.mime);
	if( ret != SQLITE_OK )
	{
		DPRINTF(E_ERROR, L_METADATA, "Error inserting details for '%s'!\n", path);
		ret = 0;
	}
	else
	{
		ret = sqlite3_last_insert_rowid(db);
	}
	free_metadata(&m, FLAG_MIME | FLAG_RESOLUTION);

	return ret;
}

static int64_t
GetTiffImageMetadata(const char *path, char *name)
{
	FILE *file;
	uint32_t width=0, height=0;
	int thumb=0;
	struct stat statbuf;
	int64_t ret;
	metadata_t m;
	memset(&m, '\0', sizeof(metadata_t));
	uint8_t tagbuf[12];
	uint32_t free_flags = 0xFFFFFFFF;
	int is_little_endian;
	uint32_t ifd_offset;
	uint32_t date_offset = 0;
	uint16_t nb_entries;
	uint16_t entry_index;
	uint16_t entry_tag;
	uint16_t entry_type;
	uint32_t entry_count;
	uint32_t entry_value;
	char b[1024];
	char file_name[MAXPATHLEN];	
			
	//DPRINTF (E_WARN, L_METADATA, "-- %s\n", path);
			
	strcpy(file_name, name);

	if ( stat(path, &statbuf) != 0 )
		return 0;
	strip_ext(name);

	if ((file = fopen (path, "rb")) == (FILE *)NULL)
	{
		DPRINTF (E_ERROR, L_METADATA, "Error opening \"%s\": %s\n",
				path, strerror (errno));
		return 0;
	}

	if (fread (tagbuf, 1, 8, file) != 8)
	{
		fclose (file);
		return 0;
	}

	// Motorola, i.e. big endian
	if (!memcmp (tagbuf, "MM\x00\x2a", 4))
		is_little_endian = 0;
	// Intel, i.e. little endian
	else if (!memcmp (tagbuf, "II\x2a\x00", 4))
		is_little_endian = 1;
	else
	{
		DPRINTF (E_WARN, L_METADATA,
				"\"%s\" not a TIFF file.\n", path);
		fclose (file);
		return 0;
	}

	//DPRINTF (E_WARN, L_METADATA, "%s endian\n", is_little_endian ? "little" : "big");

	ifd_offset =
		is_little_endian
		? tagbuf[4] | tagbuf[5]<<8 | tagbuf[6]<<16 | tagbuf[7]<<24
		: tagbuf[7] | tagbuf[6]<<8 | tagbuf[5]<<16 | tagbuf[4]<<24;

	//DPRINTF (E_WARN, L_METADATA, "IFD offset: %d\n", ifd_offset);

	if (fseek (file, ifd_offset, SEEK_SET))
	{
		DPRINTF (E_WARN, L_METADATA,
				"%s: Seek error.\n", path);
		fclose (file);
		return 0;
	}

	if (fread (tagbuf, 1, 2, file) != 2)
	{
		fclose (file);
		return 0;
	}

	nb_entries =
		is_little_endian
		? tagbuf[0] | tagbuf[1]<<8
		: tagbuf[1] | tagbuf[0]<<8;

	//DPRINTF (E_WARN, L_METADATA, "nb entries: %d\n", nb_entries);

	entry_index = 0;
	while (entry_index < nb_entries)
	{
		if (fread (tagbuf, 1, 12, file) != 12)
		{
			fclose (file);
			return 0;
		}

		// 0x100 is width, 0x101 is height and 0x132 is date created
		entry_tag =
			is_little_endian
			? tagbuf[0] | tagbuf[1]<<8
			: tagbuf[1] | tagbuf[0]<<8;

		//DPRINTF (E_WARN, L_METADATA, "entry tag: %.4x\n", entry_tag);

		// 3 is short, 4 is long
		entry_type =
			is_little_endian
			? tagbuf[2] | tagbuf[3]<<8
			: tagbuf[3] | tagbuf[2]<<8;

		//DPRINTF (E_WARN, L_METADATA, "entry type: %.4x\n", entry_type);

		// count
		entry_count =
			is_little_endian
			? tagbuf[4] | tagbuf[5]<<8 | tagbuf[6]<<16 | tagbuf[7]<<24
			: tagbuf[7] | tagbuf[6]<<8 | tagbuf[5]<<16 | tagbuf[4]<<24;

		//DPRINTF (E_WARN, L_METADATA, "entry count: %d\n", entry_count);
		
		if(entry_type == 3) // short
		{
			entry_value = is_little_endian
							? tagbuf[8] | tagbuf[9]<<8
							: tagbuf[9] | tagbuf[8]<<8;
		}
		else
		{
			entry_value = is_little_endian
							? tagbuf[ 8] | tagbuf[ 9]<<8 | tagbuf[10]<<16 | tagbuf[11]<<24
							: tagbuf[11] | tagbuf[10]<<8 | tagbuf[ 9]<<16 | tagbuf[ 8]<<24;
		}

		//DPRINTF (E_WARN, L_METADATA, "entry value: %d\n", entry_value);

		if (entry_tag == 0x100)
		{
			width = entry_value;
		}
		else if (entry_tag == 0x101)
		{
			height = entry_value;
		}
		else if(entry_tag == 0x132)   
		{
			date_offset = entry_value;
		}
		
		entry_index++;
	}
	
	if (date_offset != 0)
	{
		char date[20];
		fseek(file, date_offset, SEEK_SET);
		fgets(date, 20, file);
		m.date = strdup(date);
		m.date[4] = '-';
		m.date[7] = '-';
		m.date[10] = 'T';				
	}

	fclose (file);

	// TODO: parse Exif too, for date, location

	if (width == 0 || height == 0)
	{
		DPRINTF (E_WARN, L_METADATA, "%s: could not find width and height in TIFF header.\n", path);
		free_metadata (&m, free_flags);
		return 0;
		
	}

	xasprintf(&m.resolution, "%dx%d", (int)width, (int)height);
	m.rotation = 0;
	thumb = 0;
	m.dlna_pn = NULL;
	m.mime = strdup("image/tiff");

	if (!m.title)
		m.title = strdup (name);
		
	if(m.date == NULL)
	{
		char date[20];
		getDateFromNFO(path, file_name, date);
		if(date[0] == '\0')
		{
			free(m.date);
			m.date = NULL;		
		}
		else
		{
			m.date = strdup(date);
			m.date[10] = 'T';
		}
	}
	
	//DEBUG DPRINTF(E_DEBUG, L_METADATA, " * date: %s\n", m.date);	

	DPRINTF (E_MAXDEBUG, L_METADATA,
			"Processed \"%s\":\n  Name: %s\n  Resolution: %s\n",
			path, name, m.resolution);

	ret = sql_exec(db, "INSERT into DETAILS"
	                   " (PATH, TITLE, SIZE, TIMESTAMP, DATE, RESOLUTION,"
	                    " ROTATION, THUMBNAIL, CREATOR, DLNA_PN, MIME) "
	                   "VALUES"
	                   " (%Q, '%q', %lld, %lld, %Q, %Q, %u, %d, %Q, %Q, %Q);",
	                   path, m.title, (long long)statbuf.st_size,
					   (long long)statbuf.st_mtime, m.date, m.resolution,
					   m.rotation, thumb, m.creator, m.dlna_pn, m.mime);
	if( ret != SQLITE_OK )
	{
		DPRINTF(E_ERROR, L_METADATA, "Error inserting details for '%s'!\n", path);
		ret = 0;
	}
	else
	{
		ret = sqlite3_last_insert_rowid(db);
	}
	free_metadata(&m, free_flags);

	return ret;
}

int GetExifCoordinates( char *path, unsigned int *offset, unsigned int *size );

static int64_t
GetHEICImageMetadata(const char *path, char *name)
{
        FILE *file;
        uint32_t width=0, height=0;
        int thumb=0;
        struct stat statbuf;
        int64_t ret;
        metadata_t m;
        memset(&m, '\0', sizeof(metadata_t));
        uint8_t tagbuf[8192];
        uint32_t free_flags = 0xFFFFFFFF;
        unsigned int exif_offset = 0;
        unsigned int exif_size = 0; 
	ExifData *ed;
	ExifEntry *e = NULL;
	char latitude[14]  = "NULL";
	char longitude[14] = "NULL";
	char altitude[14]  = "NULL";
	char make[32], model[64] = {'\0'};
	char b[1024];
	char file_name[MAXPATHLEN];	

        //DPRINTF (E_WARN, L_METADATA, "-- %s\n", path);
        	
		strcpy(file_name, name);

        if ( stat(path, &statbuf) != 0 )
                return 0;
        strip_ext(name);

        int retval = GetExifCoordinates( path, &exif_offset, &exif_size );
        if( retval != 0 ) {
            DPRINTF (E_WARN, L_METADATA, "%s: could not find exif.\n", path);
            return 0;
        }
        if( !exif_offset || !exif_size ) {
            DPRINTF (E_WARN, L_METADATA, "Exif offset or size is zero.\n" );
            return 0;
        }
        if( exif_size > 8100 ) {
            DPRINTF (E_WARN, L_METADATA, "Exif size is too big: %d.\n", exif_size );
            return 0;
        }

        if ((file = fopen (path, "rb")) == (FILE *)NULL)
        {
                DPRINTF (E_ERROR, L_METADATA, "Error opening \"%s\": %s\n",
                                path, strerror (errno));
                return 0;
        }

        if (fseek (file, exif_offset, SEEK_SET) == -1)
        {
            DPRINTF (E_WARN, L_METADATA, "Can't go to offset: %d.\n", exif_offset );
            fclose (file);
            return 0;
        }

        if (fread (tagbuf, 1, 4, file) != 4)
        {
            DPRINTF (E_WARN, L_METADATA, "Can't read Exif length\n" );
            fclose (file);
            return 0;
        }
        //The length of the "Exif" string 
        if (memcmp (tagbuf, "\x00\x00\x00\x06", 4)) {
            DPRINTF (E_WARN, L_METADATA, "Invalid Exif string length %d %d %d %d\n", tagbuf[0], tagbuf[1], tagbuf[2], tagbuf[3] );
            fclose (file);
            return 0;
        }

        if (fread (tagbuf, 1, exif_size, file) != exif_size)
        {
            DPRINTF (E_WARN, L_METADATA, "Can't read Exif data\n" );
            fclose (file);
            return 0;
        }
        fclose (file);

	/* MIME hard-coded to JPEG for now */
	m.mime = strdup("image/jpeg");

	ed = exif_data_new_from_data( tagbuf, exif_size );
	if( !ed ) {
            DPRINTF (E_WARN, L_METADATA, "Can't load Exif data as exif \n" );
            return 0;
        }

        exif_data_dump( ed );

	e = exif_content_get_entry (ed->ifd[EXIF_IFD_EXIF], EXIF_TAG_DATE_TIME_ORIGINAL);
	if( e || (e = exif_content_get_entry(ed->ifd[EXIF_IFD_EXIF], EXIF_TAG_DATE_TIME_DIGITIZED)) )
	{
		m.date = strdup(exif_entry_get_value(e, b, sizeof(b)));
		if( strlen(m.date) > 10 )
		{
			m.date[4] = '-';
			m.date[7] = '-';
			m.date[10] = 'T';
		}
		else {
			free(m.date);
			m.date = NULL;
		}
	}
	
	if(m.date == NULL)
	{
		char date[20];
		getDateFromNFO(path, file_name, date);
		if(date[0] == '\0')
		{
			free(m.date);
			m.date = NULL;		
		}
		else
		{
			m.date = strdup(date);
			m.date[10] = 'T';
		}
	}
		
	//DPRINTF(E_DEBUG, L_METADATA, " * date: %s\n", m.date);

	e = exif_content_get_entry (ed->ifd[EXIF_IFD_EXIF], EXIF_TAG_PIXEL_X_DIMENSION);
	if( e )
	{
                width = exif_get_long(e->data, exif_data_get_byte_order(ed));
	}
	e = exif_content_get_entry (ed->ifd[EXIF_IFD_EXIF], EXIF_TAG_PIXEL_Y_DIMENSION);
	if( e )
	{
                height = exif_get_long(e->data, exif_data_get_byte_order(ed));
	}
	//DPRINTF(E_DEBUG, L_METADATA, " Width: %d - Height: %d\n", width, height );

	e = exif_content_get_entry(ed->ifd[EXIF_IFD_0], EXIF_TAG_MAKE);
	if( e )
	{
		strncpyt(make, exif_entry_get_value(e, b, sizeof(b)), sizeof(make));
		e = exif_content_get_entry(ed->ifd[EXIF_IFD_0], EXIF_TAG_MODEL);
		if( e )
		{
			strncpyt(model, exif_entry_get_value(e, b, sizeof(b)), sizeof(model));
			if( !strcasestr(model, make) )
				snprintf(model, sizeof(model), "%s %s", make, exif_entry_get_value(e, b, sizeof(b)));
			m.creator = escape_tag(trim(model), 1);
		}
	}
	//DPRINTF(E_DEBUG, L_METADATA, " * model: %s\n", model);

	e = exif_content_get_entry(ed->ifd[EXIF_IFD_0], EXIF_TAG_ORIENTATION);
	if( e )
	{
		switch( exif_get_short(e->data, exif_data_get_byte_order(ed)) )
		{
		case 3:
			m.rotation = 180;
			break;
		case 6:
			m.rotation = 90;
			break;
		case 8:
			m.rotation = 270;
			break;
		default:
			m.rotation = 0;
			break;
		}
	}

	double lat, lon, alt;
	extract_geolocation(ed, &lat, &lon, &alt);
	if (lat != 999999.0) sprintf(latitude,  "%.8f", lat);
	if (lon != 999999.0) sprintf(longitude, "%.8f", lon);
	if (alt != 999999.0) sprintf(altitude,  "%.8f", alt);
	//DPRINTF(E_DEBUG, L_METADATA, " * MOSDEBUG6 lat: %s, lon:%s, alt:%s\n", latitude, longitude, altitude );

	exif_data_unref(ed);

        if (width == 0 || height == 0)
        {
                DPRINTF (E_WARN, L_METADATA, "%s: could not find width and height in TIFF header.\n", path);
//                free_metadata (&m, free_flags);
//                return 0;

        }

        xasprintf(&m.resolution, "%dx%d", (int)width, (int)height);
        thumb = 0;
        m.dlna_pn = NULL;

        if (!m.title)
                m.title = strdup (name);

        //DPRINTF (E_MAXDEBUG, L_METADATA,
        //                "Processed \"%s\":\n  Name: %s\n  Resolution: %s\n",
        //                path, name, m.resolution);

	ret = sql_exec(db, "INSERT into DETAILS"
	                   " (PATH, TITLE, SIZE, TIMESTAMP, DATE, RESOLUTION,"
	                    " ROTATION, THUMBNAIL, CREATOR, DLNA_PN, MIME, LATITUDE, LONGITUDE, ALTITUDE) "
	                   "VALUES"
	                   " (%Q, '%q', %lld, %lld, %Q, %Q, %u, %d, %Q, %Q, %Q, %s, %s, %s);",
	                   path, name, (long long)statbuf.st_size, (long long)statbuf.st_mtime, m.date,
	                   m.resolution, m.rotation, thumb, m.creator, m.dlna_pn, m.mime,
	                   latitude, longitude, altitude);

        if( ret != SQLITE_OK )
        {
                DPRINTF(E_ERROR, L_METADATA, "Error inserting details for '%s'!\n", path);
                ret = 0;
        }
        else
        {
                ret = sqlite3_last_insert_rowid(db);
        }
        free_metadata(&m, free_flags);

        return ret;
}

static int64_t
GetCrwImageMetadata(const char *path, char *name)
{
	FILE *file;
	// uint32_t width=0, height=0;
	// int thumb=0;
	struct stat statbuf;
	int64_t ret;
	metadata_t m;
	memset(&m, '\0', sizeof(metadata_t));
	// uint8_t tagbuf[12];
	uint32_t free_flags = 0xFFFFFFFF;
	// int is_little_endian;
	// uint32_t ifd_offset;
	// uint32_t date_offset = 0;
	// uint16_t nb_entries;
	// uint16_t entry_index;
	// uint16_t entry_tag;
	// uint16_t entry_type;
	// uint32_t entry_count;
	// uint32_t entry_value;
	// char b[1024];
	char file_name[MAXPATHLEN];	
			
	//DPRINTF (E_WARN, L_METADATA, "-- %s\n", path);
			
	strcpy(file_name, name);

	if ( stat(path, &statbuf) != 0 )
		return 0;
	strip_ext(name);

	// if ((file = fopen (path, "rb")) == (FILE *)NULL)
	// {
	// 	DPRINTF (E_ERROR, L_METADATA, "Error opening \"%s\": %s\n",
	// 			path, strerror (errno));
	// 	return 0;
	// }

	// if (fread (tagbuf, 1, 8, file) != 8)
	// {
	// 	fclose (file);
	// 	return 0;
	// }

	// // Motorola, i.e. big endian
	// if (!memcmp (tagbuf, "MM\x00\x2a", 4))
	// 	is_little_endian = 0;
	// // Intel, i.e. little endian
	// else if (!memcmp (tagbuf, "II\x2a\x00", 4))
	// 	is_little_endian = 1;
	// else
	// {
	// 	DPRINTF (E_WARN, L_METADATA,
	// 			"\"%s\" not a TIFF file.\n", path);
	// 	fclose (file);
	// 	return 0;
	// }

	//DPRINTF (E_WARN, L_METADATA, "%s endian\n", is_little_endian ? "little" : "big");

	// ifd_offset =
	// 	is_little_endian
	// 	? tagbuf[4] | tagbuf[5]<<8 | tagbuf[6]<<16 | tagbuf[7]<<24
	// 	: tagbuf[7] | tagbuf[6]<<8 | tagbuf[5]<<16 | tagbuf[4]<<24;

	//DPRINTF (E_WARN, L_METADATA, "IFD offset: %d\n", ifd_offset);

	// if (fseek (file, ifd_offset, SEEK_SET))
	// {
	// 	DPRINTF (E_WARN, L_METADATA,
	// 			"%s: Seek error.\n", path);
	// 	fclose (file);
	// 	return 0;
	// }

	// if (fread (tagbuf, 1, 2, file) != 2)
	// {
	// 	fclose (file);
	// 	return 0;
	// }

	// nb_entries =
	// 	is_little_endian
	// 	? tagbuf[0] | tagbuf[1]<<8
	// 	: tagbuf[1] | tagbuf[0]<<8;

	//DPRINTF (E_WARN, L_METADATA, "nb entries: %d\n", nb_entries);

	// entry_index = 0;
	// while (entry_index < nb_entries)
	// {
	// 	if (fread (tagbuf, 1, 12, file) != 12)
	// 	{
	// 		fclose (file);
	// 		return 0;
	// 	}

	// 	// 0x100 is width, 0x101 is height and 0x132 is date created
	// 	entry_tag =
	// 		is_little_endian
	// 		? tagbuf[0] | tagbuf[1]<<8
	// 		: tagbuf[1] | tagbuf[0]<<8;

	// 	//DPRINTF (E_WARN, L_METADATA, "entry tag: %.4x\n", entry_tag);

	// 	// 3 is short, 4 is long
	// 	entry_type =
	// 		is_little_endian
	// 		? tagbuf[2] | tagbuf[3]<<8
	// 		: tagbuf[3] | tagbuf[2]<<8;

	// 	//DPRINTF (E_WARN, L_METADATA, "entry type: %.4x\n", entry_type);

	// 	// count
	// 	entry_count =
	// 		is_little_endian
	// 		? tagbuf[4] | tagbuf[5]<<8 | tagbuf[6]<<16 | tagbuf[7]<<24
	// 		: tagbuf[7] | tagbuf[6]<<8 | tagbuf[5]<<16 | tagbuf[4]<<24;

	// 	//DPRINTF (E_WARN, L_METADATA, "entry count: %d\n", entry_count);
		
	// 	if(entry_type == 3) // short
	// 	{
	// 		entry_value = is_little_endian
	// 						? tagbuf[8] | tagbuf[9]<<8
	// 						: tagbuf[9] | tagbuf[8]<<8;
	// 	}
	// 	else
	// 	{
	// 		entry_value = is_little_endian
	// 						? tagbuf[ 8] | tagbuf[ 9]<<8 | tagbuf[10]<<16 | tagbuf[11]<<24
	// 						: tagbuf[11] | tagbuf[10]<<8 | tagbuf[ 9]<<16 | tagbuf[ 8]<<24;
	// 	}

	// 	//DPRINTF (E_WARN, L_METADATA, "entry value: %d\n", entry_value);

	// 	if (entry_tag == 0x100)
	// 	{
	// 		width = entry_value;
	// 	}
	// 	else if (entry_tag == 0x101)
	// 	{
	// 		height = entry_value;
	// 	}
	// 	else if(entry_tag == 0x132)   
	// 	{
	// 		date_offset = entry_value;
	// 	}
		
	// 	entry_index++;
	// }
	
	// if (date_offset != 0)
	// {
	// 	char date[20];
	// 	fseek(file, date_offset, SEEK_SET);
	// 	fgets(date, 20, file);
	// 	m.date = strdup(date);
	// 	m.date[4] = '-';
	// 	m.date[7] = '-';
	// 	m.date[10] = 'T';				
	// }

	// fclose (file);

	// // TODO: parse Exif too, for date, location

	// if (width == 0 || height == 0)
	// {
	// 	DPRINTF (E_WARN, L_METADATA, "%s: could not find width and height in TIFF header.\n", path);
	// 	free_metadata (&m, free_flags);
	// 	return 0;
		
	// }

	// xasprintf(&m.resolution, "%dx%d", (int)width, (int)height);
	// m.rotation = 0;
	// thumb = 0;
	m.dlna_pn = NULL;
	m.mime = strdup("image/x-canon-crw");

	if (!m.title)
		m.title = strdup (name);
		
	// if(m.date == NULL)
	// {
	// 	char date[20];
	// 	getDateFromNFO(path, file_name, date);
	// 	if(date[0] == '\0')
	// 	{
	// 		free(m.date);
	// 		m.date = NULL;		
	// 	}
	// 	else
	// 	{
	// 		m.date = strdup(date);
	// 		m.date[10] = 'T';
	// 	}
	// }
	
	//DEBUG DPRINTF(E_DEBUG, L_METADATA, " * date: %s\n", m.date);	

	// DPRINTF (E_MAXDEBUG, L_METADATA,
	// 		"Processed \"%s\":\n  Name: %s\n  Resolution: %s\n",
	// 		path, name, m.resolution);

	ret = sql_exec(db, "INSERT into DETAILS"
	                   " (PATH, TITLE, SIZE, TIMESTAMP, CREATOR, DLNA_PN, MIME) "
	                   "VALUES"
	                   " (%Q, '%q', %lld, %lld, %Q, %Q, %Q);",
	                   path, m.title, (long long)statbuf.st_size,
					   (long long)statbuf.st_mtime, m.creator, m.dlna_pn, m.mime);
	if( ret != SQLITE_OK )
	{
		DPRINTF(E_ERROR, L_METADATA, "Error inserting details for '%s'!\n", path);
		ret = 0;
	}
	else
	{
		ret = sqlite3_last_insert_rowid(db);
	}
	free_metadata(&m, free_flags);

	return ret;
}

int64_t
GetImageMetadata(const char *path, char *name)
{
	if (ends_with (path, ".jpg") || ends_with (path, ".jpeg"))
	{
		return GetJpegImageMetadata (path, name);
	}
	else if (ends_with (path, ".png"))
	{
		return GetPngImageMetadata (path, name);
	}
	else if (ends_with (path, ".gif"))
	{
		return GetGifImageMetadata (path, name);
	}
	else if (ends_with (path, ".bmp"))
	{
		return GetBmpImageMetadata (path, name);
	}
	else if (ends_with (path, ".tif") || ends_with (path, ".tiff"))
	{
		return GetTiffImageMetadata (path, name);
	}
	else if (ends_with (path, ".heic") || ends_with (path, ".heif"))
	{
		return GetHEICImageMetadata (path, name);
	}
	else if (ends_with (path, ".crw") || ends_with (path, ".CRW"))
	{
		return GetCrwImageMetadata (path, name);
	}
	else
		return 0;
}

int64_t
GetVideoMetadata(const char *path, char *name)
{
	struct stat file;
	int ret, i;
	AVFormatContext *ctx = NULL;
	AVCodecContext *ac = NULL, *vc = NULL;
	int audio_stream = -1, video_stream = -1;
	enum audio_profiles audio_profile = PROFILE_AUDIO_UNKNOWN;
	char fourcc[4];
	int64_t album_art = 0;
	char nfo[MAXPATHLEN], *ext;
	struct song_metadata video;
	metadata_t m;
	char latitude[14]  = "NULL";
	char longitude[14] = "NULL";
	char altitude[14]  = "NULL";
	uint32_t free_flags = 0xFFFFFFFF;
	char *path_cpy, *basepath;
	char file_name[MAXPATHLEN];

	memset(&m, '\0', sizeof(m));
	memset(&video, '\0', sizeof(video));
			
	strcpy(file_name, name);

	//DEBUG DPRINTF(E_DEBUG, L_METADATA, "Parsing video %s...\n", name);
	if ( stat(path, &file) != 0 )
		return 0;
	strip_ext(name);
	//DEBUG DPRINTF(E_DEBUG, L_METADATA, " * size: %jd\n", file.st_size);

	ret = lav_open(&ctx, path);
	if( ret != 0 )
	{
		char err[128];
		av_strerror(ret, err, sizeof(err));
		DPRINTF(E_WARN, L_METADATA, "Opening %s failed! [%s]\n", path, err);
		return 0;
	}
	//dump_format(ctx, 0, NULL, 0);
        
        //Kwilt - If jpeg is found return false so the extension can be fixed
        if( ctx->iformat && strcmp( ctx->iformat->name, "jpeg_pipe" ) == 0 ) {
	    DPRINTF(E_WARN, L_METADATA, "JPEG encountered as Video: %s!\n", path );
            lav_close(ctx);
            return 0;
        }

	for( i=0; i<ctx->nb_streams; i++)
	{
		if( audio_stream == -1 &&
		    ctx->streams[i]->codec->codec_type == AVMEDIA_TYPE_AUDIO )
		{
			audio_stream = i;
			ac = ctx->streams[audio_stream]->codec;
			continue;
		}
		else if( video_stream == -1 &&
		         !lav_is_thumbnail_stream(ctx->streams[i], &m.thumb_data, &m.thumb_size) &&
			 ctx->streams[i]->codec->codec_type == AVMEDIA_TYPE_VIDEO )
		{
			video_stream = i;
			vc = ctx->streams[video_stream]->codec;
			continue;
		}
	}
	path_cpy = strdup(path);
	basepath = basename(path_cpy);
	if( !vc )
	{
		/* This must not be a video file. */
		lav_close(ctx);
		if( !is_audio(path) )
			DPRINTF(E_DEBUG, L_METADATA, "File %s does not contain a video stream.\n", basepath);
		free(path_cpy);
		return 0;
	}

	if( ac )
	{
		aac_object_type_t aac_type = AAC_INVALID;
		switch( ac->codec_id )
		{
			case AV_CODEC_ID_MP3:
				audio_profile = PROFILE_AUDIO_MP3;
				break;
			case AV_CODEC_ID_AAC:
				if( !ac->extradata_size ||
				    !ac->extradata )
				{
					DPRINTF(E_DEBUG, L_METADATA, "No AAC type\n");
				}
				else
				{
					uint8_t data;
					memcpy(&data, ac->extradata, 1);
					aac_type = data >> 3;
				}
				switch( aac_type )
				{
					/* AAC Low Complexity variants */
					case AAC_LC:
					case AAC_LC_ER:
						if( ac->sample_rate < 8000 ||
						    ac->sample_rate > 48000 )
						{
							DPRINTF(E_DEBUG, L_METADATA, "Unsupported AAC: sample rate is not 8000 < %d < 48000\n",
								ac->sample_rate);
							break;
						}
						/* AAC @ Level 1/2 */
						if( ac->channels <= 2 &&
						    ac->bit_rate <= 576000 )
							audio_profile = PROFILE_AUDIO_AAC;
						else if( ac->channels <= 6 &&
							 ac->bit_rate <= 1440000 )
							audio_profile = PROFILE_AUDIO_AAC_MULT5;
						else
							DPRINTF(E_DEBUG, L_METADATA, "Unhandled AAC: %d channels, %d bitrate\n",
								ac->channels,
								ac->bit_rate);
						break;
					default:
						DPRINTF(E_DEBUG, L_METADATA, "Unhandled AAC type [%d]\n", aac_type);
						break;
				}
				break;
			case AV_CODEC_ID_AC3:
			case AV_CODEC_ID_DTS:
				audio_profile = PROFILE_AUDIO_AC3;
				break;
			case AV_CODEC_ID_WMAV1:
			case AV_CODEC_ID_WMAV2:
				/* WMA Baseline: stereo, up to 48 KHz, up to 192,999 bps */
				if ( ac->bit_rate <= 193000 )
					audio_profile = PROFILE_AUDIO_WMA_BASE;
				/* WMA Full: stereo, up to 48 KHz, up to 385 Kbps */
				else if ( ac->bit_rate <= 385000 )
					audio_profile = PROFILE_AUDIO_WMA_FULL;
				break;
			case AV_CODEC_ID_WMAPRO:
				audio_profile = PROFILE_AUDIO_WMA_PRO;
				break;
			case AV_CODEC_ID_MP2:
				audio_profile = PROFILE_AUDIO_MP2;
				break;
			case AV_CODEC_ID_AMR_NB:
				audio_profile = PROFILE_AUDIO_AMR;
				break;
			default:
				if( (ac->codec_id >= AV_CODEC_ID_PCM_S16LE) &&
				    (ac->codec_id < AV_CODEC_ID_ADPCM_IMA_QT) )
					audio_profile = PROFILE_AUDIO_PCM;
				else
					DPRINTF(E_DEBUG, L_METADATA, "Unhandled audio codec [0x%X]\n", ac->codec_id);
				break;
		}
		m.frequency = ac->sample_rate;
		m.channels = ac->channels;
	}
	if( vc )
	{
		int off;
		int duration, hours, min, sec, ms;
		ts_timestamp_t ts_timestamp = NONE;
		DPRINTF(E_DEBUG, L_METADATA, "Container: '%s' [%s]\n", ctx->iformat->name, basepath);
		xasprintf(&m.resolution, "%dx%d", vc->width, vc->height);
		if( ctx->bit_rate > 8 )
			m.bitrate = ctx->bit_rate / 8;
		if( ctx->duration > 0 ) {
			duration = (int)(ctx->duration / AV_TIME_BASE);
			hours = (int)(duration / 3600);
			min = (int)(duration / 60 % 60);
			sec = (int)(duration % 60);
			ms = (int)(ctx->duration / (AV_TIME_BASE/1000) % 1000);
			xasprintf(&m.duration, "%d:%02d:%02d.%03d", hours, min, sec, ms);
		}

		/* NOTE: The DLNA spec only provides for ASF (WMV), TS, PS, and MP4 containers.
		 * Skip DLNA parsing for everything else. */
		if( strcmp(ctx->iformat->name, "avi") == 0 )
		{
			xasprintf(&m.mime, "video/x-msvideo");
			if( vc->codec_id == AV_CODEC_ID_MPEG4 )
			{
        			fourcc[0] = vc->codec_tag     & 0xff;
			        fourcc[1] = vc->codec_tag>>8  & 0xff;
		        	fourcc[2] = vc->codec_tag>>16 & 0xff;
			        fourcc[3] = vc->codec_tag>>24 & 0xff;
				if( memcmp(fourcc, "XVID", 4) == 0 ||
				    memcmp(fourcc, "DX50", 4) == 0 ||
				    memcmp(fourcc, "DIVX", 4) == 0 )
					xasprintf(&m.creator, "DiVX");
			}
		}
		else if( strcmp(ctx->iformat->name, "mov,mp4,m4a,3gp,3g2,mj2") == 0 &&
		         ends_with(path, ".mov") )
			xasprintf(&m.mime, "video/quicktime");
		else if( strncmp(ctx->iformat->name, "matroska", 8) == 0 )
		{
			if( ends_with(path, ".webm") )
				xasprintf(&m.mime, "video/webm");
			else
				xasprintf(&m.mime, "video/x-matroska");
		}
		else if( strcmp(ctx->iformat->name, "flv") == 0 )
			xasprintf(&m.mime, "video/x-flv");
		else if( strcmp(ctx->iformat->name, "dv") == 0 )
			xasprintf(&m.mime, "video/x-dv");
		else if( strcmp(ctx->iformat->name, "rm") == 0 )
			xasprintf(&m.mime, "application/vnd.rn-realmedia");
		else if( strcmp(ctx->iformat->name, "ogg") == 0 )
			xasprintf(&m.mime, "video/ogg");
		if( m.mime )
			goto video_no_dlna;

                //Kwilt - Skip parsing dlna_n
		goto video_no_dlna;

		switch( vc->codec_id )
		{
			case AV_CODEC_ID_MPEG1VIDEO:
				if( strcmp(ctx->iformat->name, "mpeg") == 0 )
				{
					if( (vc->width  == 352) &&
					    (vc->height <= 288) )
					{
						m.dlna_pn = strdup("MPEG1");
					}
					xasprintf(&m.mime, "video/mpeg");
				}
				break;
			case AV_CODEC_ID_MPEG2VIDEO:
				m.dlna_pn = malloc(64);
				off = sprintf(m.dlna_pn, "MPEG_");
				if( strcmp(ctx->iformat->name, "mpegts") == 0 )
				{
					int raw_packet_size;
					int dlna_ts_present = dlna_timestamp_is_present(path, &raw_packet_size);
					DPRINTF(E_DEBUG, L_METADATA, "Stream %d of %s is %s MPEG2 TS packet size %d\n",
						video_stream, basepath, m.resolution, raw_packet_size);
					off += sprintf(m.dlna_pn+off, "TS_");
					if( (vc->width  >= 1280) &&
					    (vc->height >= 720) )
					{
						off += sprintf(m.dlna_pn+off, "HD_NA");
					}
					else
					{
						off += sprintf(m.dlna_pn+off, "SD_");
						if( (vc->height == 576) ||
						    (vc->height == 288) )
							off += sprintf(m.dlna_pn+off, "EU");
						else
							off += sprintf(m.dlna_pn+off, "NA");
					}
					if( raw_packet_size == MPEG_TS_PACKET_LENGTH_DLNA )
					{
						if (dlna_ts_present)
							ts_timestamp = VALID;
						else
							ts_timestamp = EMPTY;
					}
					else if( raw_packet_size != MPEG_TS_PACKET_LENGTH )
					{
						DPRINTF(E_DEBUG, L_METADATA, "Unsupported DLNA TS packet size [%d] (%s)\n",
							raw_packet_size, basepath);
						free(m.dlna_pn);
						m.dlna_pn = NULL;
					}
					switch( ts_timestamp )
					{
						case NONE:
							xasprintf(&m.mime, "video/mpeg");
							if( m.dlna_pn )
								off += sprintf(m.dlna_pn+off, "_ISO");
							break;
						case VALID:
							off += sprintf(m.dlna_pn+off, "_T");
						case EMPTY:
							xasprintf(&m.mime, "video/vnd.dlna.mpeg-tts");
						default:
							break;
					}
				}
				else if( strcmp(ctx->iformat->name, "mpeg") == 0 )
				{
					DPRINTF(E_DEBUG, L_METADATA, "Stream %d of %s is %s MPEG2 PS\n",
						video_stream, basepath, m.resolution);
					off += sprintf(m.dlna_pn+off, "PS_");
					if( (vc->height == 576) ||
					    (vc->height == 288) )
						off += sprintf(m.dlna_pn+off, "PAL");
					else
						off += sprintf(m.dlna_pn+off, "NTSC");
					xasprintf(&m.mime, "video/mpeg");
				}
				else
				{
					DPRINTF(E_DEBUG, L_METADATA, "Stream %d of %s [%s] is %s non-DLNA MPEG2\n",
						video_stream, basepath, ctx->iformat->name, m.resolution);
					free(m.dlna_pn);
					m.dlna_pn = NULL;
				}
				break;
			case AV_CODEC_ID_H264:
				m.dlna_pn = malloc(128);
				off = sprintf(m.dlna_pn, "AVC_");

				if( strcmp(ctx->iformat->name, "mpegts") == 0 )
				{
					AVRational display_aspect_ratio;
					int fps, interlaced;
					int raw_packet_size;
					int dlna_ts_present = dlna_timestamp_is_present(path, &raw_packet_size);

					off += sprintf(m.dlna_pn+off, "TS_");
					if (vc->sample_aspect_ratio.num) {
						av_reduce(&display_aspect_ratio.num, &display_aspect_ratio.den,
						          vc->width  * vc->sample_aspect_ratio.num,
						          vc->height * vc->sample_aspect_ratio.den,
						          1024*1024);
					}
					fps = lav_get_fps(ctx->streams[video_stream]);
					interlaced = lav_get_interlaced(vc, ctx->streams[video_stream]);
					if( ((((vc->width == 1920 || vc->width == 1440) && vc->height == 1080) ||
					      (vc->width == 720 && vc->height == 480)) && fps == 59 && interlaced) ||
					    ((vc->width == 1280 && vc->height == 720) && fps == 59 && !interlaced) )
					{
						if( (vc->profile == FF_PROFILE_H264_MAIN || vc->profile == FF_PROFILE_H264_HIGH) &&
						    audio_profile == PROFILE_AUDIO_AC3 )
						{
							off += sprintf(m.dlna_pn+off, "HD_60_");
							vc->profile = FF_PROFILE_SKIP;
						}
					}
					else if( ((vc->width == 1920 && vc->height == 1080) ||
					          (vc->width == 1440 && vc->height == 1080) ||
					          (vc->width == 1280 && vc->height ==  720) ||
					          (vc->width ==  720 && vc->height ==  576)) &&
					          interlaced && fps == 50 )
					{
						if( (vc->profile == FF_PROFILE_H264_MAIN || vc->profile == FF_PROFILE_H264_HIGH) &&
						    audio_profile == PROFILE_AUDIO_AC3 )
						{
							off += sprintf(m.dlna_pn+off, "HD_50_");
							vc->profile = FF_PROFILE_SKIP;
						}
					}
					switch( vc->profile )
					{
						case FF_PROFILE_H264_BASELINE:
						case FF_PROFILE_H264_CONSTRAINED_BASELINE:
							off += sprintf(m.dlna_pn+off, "BL_");
							if( vc->width  <= 352 &&
							    vc->height <= 288 &&
							    vc->bit_rate <= 384000 )
							{
								off += sprintf(m.dlna_pn+off, "CIF15_");
								break;
							}
							else if( vc->width  <= 352 &&
							         vc->height <= 288 &&
							         vc->bit_rate <= 3000000 )
							{
								off += sprintf(m.dlna_pn+off, "CIF30_");
								break;
							}
							/* Fall back to Main Profile if it doesn't match a Baseline DLNA profile. */
							else
								off -= 3;
						default:
						case FF_PROFILE_H264_MAIN:
							off += sprintf(m.dlna_pn+off, "MP_");
							if( vc->profile != FF_PROFILE_H264_BASELINE &&
							    vc->profile != FF_PROFILE_H264_CONSTRAINED_BASELINE &&
							    vc->profile != FF_PROFILE_H264_MAIN )
							{
								DPRINTF(E_DEBUG, L_METADATA, "Unknown AVC profile %d; assuming MP. [%s]\n",
									vc->profile, basepath);
							}
							if( vc->width  <= 720 &&
							    vc->height <= 576 &&
							    vc->bit_rate <= 10000000 )
							{
								off += sprintf(m.dlna_pn+off, "SD_");
							}
							else if( vc->width  <= 1920 &&
							         vc->height <= 1152 &&
							         vc->bit_rate <= 20000000 )
							{
								off += sprintf(m.dlna_pn+off, "HD_");
							}
							else
							{
								DPRINTF(E_DEBUG, L_METADATA, "Unsupported h.264 video profile! [%s, %dx%d, %dbps : %s]\n",
									m.dlna_pn, vc->width, vc->height, vc->bit_rate, basepath);
								free(m.dlna_pn);
								m.dlna_pn = NULL;
							}
							break;
						case FF_PROFILE_H264_HIGH:
							off += sprintf(m.dlna_pn+off, "HP_");
							if( vc->width  <= 1920 &&
							    vc->height <= 1152 &&
							    vc->bit_rate <= 30000000 &&
							    audio_profile == PROFILE_AUDIO_AC3 )
							{
								off += sprintf(m.dlna_pn+off, "HD_");
							}
							else
							{
								DPRINTF(E_DEBUG, L_METADATA, "Unsupported h.264 HP video profile! [%dbps, %d audio : %s]\n",
									vc->bit_rate, audio_profile, basepath);
								free(m.dlna_pn);
								m.dlna_pn = NULL;
							}
							break;
						case FF_PROFILE_SKIP:
							break;
					}
					if( !m.dlna_pn )
						break;
					switch( audio_profile )
					{
						case PROFILE_AUDIO_MP3:
							off += sprintf(m.dlna_pn+off, "MPEG1_L3");
							break;
						case PROFILE_AUDIO_AC3:
							off += sprintf(m.dlna_pn+off, "AC3");
							break;
						case PROFILE_AUDIO_AAC:
						case PROFILE_AUDIO_AAC_MULT5:
							off += sprintf(m.dlna_pn+off, "AAC_MULT5");
							break;
						default:
							DPRINTF(E_DEBUG, L_METADATA, "No DLNA profile found for %s file [%s]\n",
								m.dlna_pn, basepath);
							free(m.dlna_pn);
							m.dlna_pn = NULL;
							break;
					}
					if( !m.dlna_pn )
						break;
					if( raw_packet_size == MPEG_TS_PACKET_LENGTH_DLNA )
					{
						if( vc->profile == FF_PROFILE_H264_HIGH ||
						    dlna_ts_present )
							ts_timestamp = VALID;
						else
							ts_timestamp = EMPTY;
					}
					else if( raw_packet_size != MPEG_TS_PACKET_LENGTH )
					{
						DPRINTF(E_DEBUG, L_METADATA, "Unsupported DLNA TS packet size [%d] (%s)\n",
							raw_packet_size, basepath);
						free(m.dlna_pn);
						m.dlna_pn = NULL;
					}
					switch( ts_timestamp )
					{
						case NONE:
							if( m.dlna_pn )
								off += sprintf(m.dlna_pn+off, "_ISO");
							break;
						case VALID:
							off += sprintf(m.dlna_pn+off, "_T");
						case EMPTY:
							xasprintf(&m.mime, "video/vnd.dlna.mpeg-tts");
						default:
							break;
					}
				}
				else if( strcmp(ctx->iformat->name, "mov,mp4,m4a,3gp,3g2,mj2") == 0 )
				{
					off += sprintf(m.dlna_pn+off, "MP4_");

					switch( vc->profile ) {
					case FF_PROFILE_H264_BASELINE:
					case FF_PROFILE_H264_CONSTRAINED_BASELINE:
						if( vc->width  <= 352 &&
						    vc->height <= 288 )
						{
							if( ctx->bit_rate < 600000 )
								off += sprintf(m.dlna_pn+off, "BL_CIF15_");
							else if( ctx->bit_rate < 5000000 )
								off += sprintf(m.dlna_pn+off, "BL_CIF30_");
							else
								goto mp4_mp_fallback;

							if( audio_profile == PROFILE_AUDIO_AMR )
							{
								off += sprintf(m.dlna_pn+off, "AMR");
							}
							else if( audio_profile == PROFILE_AUDIO_AAC )
							{
								off += sprintf(m.dlna_pn+off, "AAC_");
								if( ctx->bit_rate < 520000 )
								{
									off += sprintf(m.dlna_pn+off, "520");
								}
								else if( ctx->bit_rate < 940000 )
								{
									off += sprintf(m.dlna_pn+off, "940");
								}
								else
								{
									off -= 13;
									goto mp4_mp_fallback;
								}
							}
							else
							{
								off -= 9;
								goto mp4_mp_fallback;
							}
						}
						else if( vc->width  <= 720 &&
						         vc->height <= 576 )
						{
							if( vc->level == 30 &&
							    audio_profile == PROFILE_AUDIO_AAC &&
							    ctx->bit_rate <= 5000000 )
								off += sprintf(m.dlna_pn+off, "BL_L3L_SD_AAC");
							else if( vc->level <= 31 &&
							         audio_profile == PROFILE_AUDIO_AAC &&
							         ctx->bit_rate <= 15000000 )
								off += sprintf(m.dlna_pn+off, "BL_L31_HD_AAC");
							else
								goto mp4_mp_fallback;
						}
						else if( vc->width  <= 1280 &&
						         vc->height <= 720 )
						{
							if( vc->level <= 31 &&
							    audio_profile == PROFILE_AUDIO_AAC &&
							    ctx->bit_rate <= 15000000 )
								off += sprintf(m.dlna_pn+off, "BL_L31_HD_AAC");
							else if( vc->level <= 32 &&
							         audio_profile == PROFILE_AUDIO_AAC &&
							         ctx->bit_rate <= 21000000 )
								off += sprintf(m.dlna_pn+off, "BL_L32_HD_AAC");
							else
								goto mp4_mp_fallback;
						}
						else
							goto mp4_mp_fallback;
						break;
					case FF_PROFILE_H264_MAIN:
					mp4_mp_fallback:
						off += sprintf(m.dlna_pn+off, "MP_");
						/* AVC MP4 SD profiles - 10 Mbps max */
						if( vc->width  <= 720 &&
						    vc->height <= 576 &&
						    vc->bit_rate <= 10000000 )
						{
							sprintf(m.dlna_pn+off, "SD_");
							if( audio_profile == PROFILE_AUDIO_AC3 )
								off += sprintf(m.dlna_pn+off, "AC3");
							else if( audio_profile == PROFILE_AUDIO_AAC ||
							         audio_profile == PROFILE_AUDIO_AAC_MULT5 )
								off += sprintf(m.dlna_pn+off, "AAC_MULT5");
							else if( audio_profile == PROFILE_AUDIO_MP3 )
								off += sprintf(m.dlna_pn+off, "MPEG1_L3");
							else
								m.dlna_pn[10] = '\0';
						}
						else if( vc->width  <= 1280 &&
						         vc->height <= 720 &&
						         vc->bit_rate <= 15000000 &&
						         audio_profile == PROFILE_AUDIO_AAC )
						{
							off += sprintf(m.dlna_pn+off, "HD_720p_AAC");
						}
						else if( vc->width  <= 1920 &&
						         vc->height <= 1080 &&
						         vc->bit_rate <= 21000000 &&
						         audio_profile == PROFILE_AUDIO_AAC )
						{
							off += sprintf(m.dlna_pn+off, "HD_1080i_AAC");
						}
						if( strlen(m.dlna_pn) <= 11 )
						{
							DPRINTF(E_DEBUG, L_METADATA, "No DLNA profile found for %s file %s\n",
								m.dlna_pn, basepath);
							free(m.dlna_pn);
							m.dlna_pn = NULL;
						}
						break;
					case FF_PROFILE_H264_HIGH:
						if( vc->width  <= 1920 &&
						    vc->height <= 1080 &&
						    vc->bit_rate <= 25000000 &&
						    audio_profile == PROFILE_AUDIO_AAC )
						{
							off += sprintf(m.dlna_pn+off, "HP_HD_AAC");
						}
						break;
					default:
						DPRINTF(E_DEBUG, L_METADATA, "AVC profile [%d] not recognized for file %s\n",
							vc->profile, basepath);
						free(m.dlna_pn);
						m.dlna_pn = NULL;
						break;
					}
				}
				else
				{
					free(m.dlna_pn);
					m.dlna_pn = NULL;
				}
				DPRINTF(E_DEBUG, L_METADATA, "Stream %d of %s is h.264\n", video_stream, basepath);
				break;
			case AV_CODEC_ID_MPEG4:
        			fourcc[0] = vc->codec_tag     & 0xff;
			        fourcc[1] = vc->codec_tag>>8  & 0xff;
			        fourcc[2] = vc->codec_tag>>16 & 0xff;
			        fourcc[3] = vc->codec_tag>>24 & 0xff;
				DPRINTF(E_DEBUG, L_METADATA, "Stream %d of %s is MPEG4 [%c%c%c%c/0x%X]\n",
					video_stream, basepath,
					isprint(fourcc[0]) ? fourcc[0] : '_',
					isprint(fourcc[1]) ? fourcc[1] : '_',
					isprint(fourcc[2]) ? fourcc[2] : '_',
					isprint(fourcc[3]) ? fourcc[3] : '_',
					vc->codec_tag);

				if( strcmp(ctx->iformat->name, "mov,mp4,m4a,3gp,3g2,mj2") == 0 )
				{
					m.dlna_pn = malloc(128);
					off = sprintf(m.dlna_pn, "MPEG4_P2_");

					if( ends_with(path, ".3gp") || ends_with(path, ".3gpp") )
					{
						xasprintf(&m.mime, "video/3gpp");
						switch( audio_profile )
						{
							case PROFILE_AUDIO_AAC:
								off += sprintf(m.dlna_pn+off, "3GPP_SP_L0B_AAC");
								break;
							case PROFILE_AUDIO_AMR:
								off += sprintf(m.dlna_pn+off, "3GPP_SP_L0B_AMR");
								break;
							default:
								DPRINTF(E_DEBUG, L_METADATA, "No DLNA profile found for MPEG4-P2 3GP/0x%X file %s\n",
								        ac->codec_id, basepath);
								free(m.dlna_pn);
								m.dlna_pn = NULL;
								break;
						}
					}
					else
					{
						if( ctx->bit_rate <= 1000000 &&
						    audio_profile == PROFILE_AUDIO_AAC )
						{
							off += sprintf(m.dlna_pn+off, "MP4_ASP_AAC");
						}
						else if( ctx->bit_rate <= 4000000 &&
						         vc->width  <= 640 &&
						         vc->height <= 480 &&
						         audio_profile == PROFILE_AUDIO_AAC )
						{
							off += sprintf(m.dlna_pn+off, "MP4_SP_VGA_AAC");
						}
						else
						{
							DPRINTF(E_DEBUG, L_METADATA, "Unsupported h.264 video profile! [%dx%d, %dbps]\n",
								vc->width,
								vc->height,
								ctx->bit_rate);
							free(m.dlna_pn);
							m.dlna_pn = NULL;
						}
					}
				}
				break;
			case AV_CODEC_ID_WMV3:
				/* I'm not 100% sure this is correct, but it works on everything I could get my hands on */
				if( vc->extradata_size > 0 )
				{
					if( !((vc->extradata[0] >> 3) & 1) )
						vc->level = 0;
					if( !((vc->extradata[0] >> 6) & 1) )
						vc->profile = 0;
				}
			case AV_CODEC_ID_VC1:
				if( strcmp(ctx->iformat->name, "asf") != 0 )
				{
					DPRINTF(E_DEBUG, L_METADATA, "Skipping DLNA parsing for non-ASF VC1 file %s\n", path);
					break;
				}
				m.dlna_pn = malloc(64);
				off = sprintf(m.dlna_pn, "WMV");
				DPRINTF(E_DEBUG, L_METADATA, "Stream %d of %s is VC1\n", video_stream, basepath);
				xasprintf(&m.mime, "video/x-ms-wmv");
				if( (vc->width  <= 176) &&
				    (vc->height <= 144) &&
				    (vc->level == 0) )
				{
					off += sprintf(m.dlna_pn+off, "SPLL_");
					switch( audio_profile )
					{
						case PROFILE_AUDIO_MP3:
							off += sprintf(m.dlna_pn+off, "MP3");
							break;
						case PROFILE_AUDIO_WMA_BASE:
							off += sprintf(m.dlna_pn+off, "BASE");
							break;
						default:
							DPRINTF(E_DEBUG, L_METADATA, "No DLNA profile found for WMVSPLL/0x%X file %s\n",
								audio_profile, basepath);
							free(m.dlna_pn);
							m.dlna_pn = NULL;
							break;
					}
				}
				else if( (vc->width  <= 352) &&
				         (vc->height <= 288) &&
				         (vc->profile == 0) &&
				         (ctx->bit_rate/8 <= 384000) )
				{
					off += sprintf(m.dlna_pn+off, "SPML_");
					switch( audio_profile )
					{
						case PROFILE_AUDIO_MP3:
							off += sprintf(m.dlna_pn+off, "MP3");
							break;
						case PROFILE_AUDIO_WMA_BASE:
							off += sprintf(m.dlna_pn+off, "BASE");
							break;
						default:
							DPRINTF(E_DEBUG, L_METADATA, "No DLNA profile found for WMVSPML/0x%X file %s\n",
								audio_profile, basepath);
							free(m.dlna_pn);
							m.dlna_pn = NULL;
							break;
					}
				}
				else if( (vc->width  <= 720) &&
				         (vc->height <= 576) &&
				         (ctx->bit_rate/8 <= 10000000) )
				{
					off += sprintf(m.dlna_pn+off, "MED_");
					switch( audio_profile )
					{
						case PROFILE_AUDIO_WMA_PRO:
							off += sprintf(m.dlna_pn+off, "PRO");
							break;
						case PROFILE_AUDIO_WMA_FULL:
							off += sprintf(m.dlna_pn+off, "FULL");
							break;
						case PROFILE_AUDIO_WMA_BASE:
							off += sprintf(m.dlna_pn+off, "BASE");
							break;
						default:
							DPRINTF(E_DEBUG, L_METADATA, "No DLNA profile found for WMVMED/0x%X file %s\n",
								audio_profile, basepath);
							free(m.dlna_pn);
							m.dlna_pn = NULL;
							break;
					}
				}
				else if( (vc->width  <= 1920) &&
				         (vc->height <= 1080) &&
				         (ctx->bit_rate/8 <= 20000000) )
				{
					off += sprintf(m.dlna_pn+off, "HIGH_");
					switch( audio_profile )
					{
						case PROFILE_AUDIO_WMA_PRO:
							off += sprintf(m.dlna_pn+off, "PRO");
							break;
						case PROFILE_AUDIO_WMA_FULL:
							off += sprintf(m.dlna_pn+off, "FULL");
							break;
						default:
							DPRINTF(E_DEBUG, L_METADATA, "No DLNA profile found for WMVHIGH/0x%X file %s\n",
								audio_profile, basepath);
							free(m.dlna_pn);
							m.dlna_pn = NULL;
							break;
					}
				}
				break;
			case AV_CODEC_ID_MSMPEG4V3:
				xasprintf(&m.mime, "video/x-msvideo");
			default:
				DPRINTF(E_DEBUG, L_METADATA, "Stream %d of %s is %s [type %d]\n",
					video_stream, basepath, m.resolution, vc->codec_id);
				break;
		}
	}

	if( strcmp(ctx->iformat->name, "asf") == 0 )
	{
		if( readtags((char *)path, &video, &file, "en_US", "asf") == 0 )
		{
			if( video.title && *video.title )
			{
				m.title = escape_tag(trim(video.title), 1);
			}
			if( video.genre && *video.genre )
			{
				m.genre = escape_tag(trim(video.genre), 1);
			}
			if( video.contributor[ROLE_TRACKARTIST] && *video.contributor[ROLE_TRACKARTIST] )
			{
				m.artist = escape_tag(trim(video.contributor[ROLE_TRACKARTIST]), 1);
			}
			if( video.contributor[ROLE_ALBUMARTIST] && *video.contributor[ROLE_ALBUMARTIST] )
			{
				m.creator = escape_tag(trim(video.contributor[ROLE_ALBUMARTIST]), 1);
			}
			else
			{
				m.creator = m.artist;
				free_flags &= ~FLAG_CREATOR;
			}
			if (!m.thumb_data)
			{
				m.thumb_data = video.image;
				m.thumb_size = video.image_size;
			}
		}
	}
	#ifndef NETGEAR
	#if LIBAVFORMAT_VERSION_INT >= ((52<<16)+(31<<8)+0)
	else if( strcmp(ctx->iformat->name, "mov,mp4,m4a,3gp,3g2,mj2") == 0 )
	{
		if( ctx->metadata )
		{
			AVDictionaryEntry *tag = NULL;

			//DEBUG DPRINTF(E_DEBUG, L_METADATA, "Metadata:\n");
			while( (tag = av_dict_get(ctx->metadata, "", tag, AV_DICT_IGNORE_SUFFIX)) )
			{
				//DEBUG DPRINTF(E_DEBUG, L_METADATA, "  %-16s: %s\n", tag->key, tag->value);
				if( strcmp(tag->key, "title") == 0 )
					m.title = escape_tag(trim(tag->value), 1);
				else if( strcmp(tag->key, "genre") == 0 )
					m.genre = escape_tag(trim(tag->value), 1);
				else if( strcmp(tag->key, "artist") == 0 )
					m.artist = escape_tag(trim(tag->value), 1);
				else if( strcmp(tag->key, "comment") == 0 )
					m.comment = escape_tag(trim(tag->value), 1);
			}
		}
	}
	#endif
	#endif
video_no_dlna:

#ifdef TIVO_SUPPORT
	if( ends_with(path, ".TiVo") && is_tivo_file(path) )
	{
		if( m.dlna_pn )
		{
			free(m.dlna_pn);
			m.dlna_pn = NULL;
		}
		m.mime = realloc(m.mime, 21);
		strcpy(m.mime, "video/x-tivo-mpeg");
	}
#endif

	strcpy(nfo, path);
	ext = strrchr(nfo, '.');
	if( ext )
	{
		strcpy(ext+1, "nfo");
		if( access(nfo, F_OK) == 0 )
		{
			parse_nfo(nfo, &m);
		}
	}

	if( !m.mime )
	{
		if( strcmp(ctx->iformat->name, "avi") == 0 )
			xasprintf(&m.mime, "video/x-msvideo");
		else if( strncmp(ctx->iformat->name, "mpeg", 4) == 0 )
			xasprintf(&m.mime, "video/mpeg");
		else if( strcmp(ctx->iformat->name, "asf") == 0 )
			xasprintf(&m.mime, "video/x-ms-wmv");
		else if( strcmp(ctx->iformat->name, "mov,mp4,m4a,3gp,3g2,mj2") == 0 )
			if( ends_with(path, ".mov") )
				xasprintf(&m.mime, "video/quicktime");
			else if( ends_with(path, ".3gp") || ends_with(path, ".3gpp") )
				xasprintf(&m.mime, "video/3gpp");
			else if( ends_with(path, ".3gp2") || ends_with(path, ".3gpp2") )
				xasprintf(&m.mime, "video/3gpp2");
			else
				xasprintf(&m.mime, "video/mp4");
		else if( strncmp(ctx->iformat->name, "matroska", 8) == 0 )
			xasprintf(&m.mime, "video/x-matroska");
		else if( strcmp(ctx->iformat->name, "flv") == 0 )
			xasprintf(&m.mime, "video/x-flv");
		else
			DPRINTF(E_WARN, L_METADATA, "%s: Unhandled format: %s\n", path, ctx->iformat->name);
	}

	#if LIBAVFORMAT_VERSION_INT >= ((52<<16)+(31<<8)+0)
	if( strcmp(ctx->iformat->name, "mov,mp4,m4a,3gp,3g2,mj2") == 0 )
	{
		if( ctx->metadata )
		{
			//DPRINTF(E_WARN, L_METADATA, "--- %s\n", name );

			AVDictionaryEntry *tag;

			// Apple location tag
			tag = av_dict_get(ctx->metadata, "com.apple.quicktime.location.ISO6709", NULL, 0);

			// Generic location tag (©xyz) (also used on older iOS devices)
			if (!tag)
				tag = av_dict_get(ctx->metadata, "location", NULL, 0);

			if (tag)
			{
				//DPRINTF(E_WARN, L_METADATA, "location: %s\n", tag->value);
				parse_iso_6709(tag->value, (char *) &latitude, (char *) &longitude, (char *) &altitude);

				//DPRINTF(E_WARN, L_METADATA, "latitude: %s\n", latitude);
				//DPRINTF(E_WARN, L_METADATA, "longitude: %s\n", longitude);
				//DPRINTF(E_WARN, L_METADATA, "altitude: %s\n", altitude);
			}

			// Apple creation date, includes timezone
			tag = av_dict_get(ctx->metadata, "com.apple.quicktime.creationdate", NULL, 0);

			// Generic creation date tag (©day) (also used on older iOS devices), includes timezone
			if (!tag)
				tag = av_dict_get(ctx->metadata, "date", NULL, 0);

			// Even more generic creation_time (not 100% sure where it comes from), no timezone, can be 1970
			if (!tag)
				tag = av_dict_get(ctx->metadata, "creation_time", NULL, 0);
				
			if (!tag)
			{
				char date[20];
				getDateFromNFO(path, file_name, date);
				m.date = malloc(20);
				if(date[0] == '\0')
				{
					free(m.date);
					m.date = NULL;		
				}
				else
				{
					m.date = strdup(date);
					m.date[10] = 'T';
				}
			}	

			// if we found a time taken tag and its value is not Epoch
			else if (tag && strncmp(tag->value, "1970-01-01T00:00:00", 19))
			{
				//DPRINTF(E_WARN, L_METADATA, "loaded time_taken: %s\n", tag->value);

				// Sample values:
				// com.apple.quicktime.creationdate: 2017-09-15T14:19:39-0400
				// date                            : 2014-09-21T18:15:54+0100
				// creation_time                   : 1970-01-01T00:00:00.000000Z

				struct tm tm;
				const char *cp;

				memset(&tm, 0, sizeof(struct tm));

				// parse date
  				cp = strptime (tag->value, "%Y-%m-%dT%H:%M:%S", &tm);

				// make sure the whole pattern was matched
				// i.e. the first unmatched char is the 20th, i.e. the char after the number of seconds
  				if (cp == tag->value + 19)
				{
					// format the date, in case it was odd but parsable (day over 31...)
					// omit the timezone offset and add quotes to escape the value
					m.date = malloc(20);
					strftime(m.date, 20, "%Y-%m-%dT%H:%M:%S", &tm);

					//DPRINTF(E_WARN, L_METADATA, "saved time_taken: %s\n", m.date);
				}
			}
		}
	}
	#endif

	if( !m.title )
		m.title = strdup(name);

	//Don't look for album art - Kwilt album_art = find_album_art(path, m.thumb_data, m.thumb_size);
	freetags(&video);
	lav_close(ctx);

	ret = sql_exec(db, "INSERT into DETAILS"
	                   " (PATH, SIZE, TIMESTAMP, DURATION, DATE, CHANNELS, BITRATE, SAMPLERATE, RESOLUTION,"
	                   "  TITLE, CREATOR, ARTIST, GENRE, COMMENT, DLNA_PN, MIME, ALBUM_ART, LATITUDE, LONGITUDE, ALTITUDE) "
	                   "VALUES"
	                   " (%Q, %lld, %lld, %Q, %Q, %u, %u, %u, %Q, '%q', %Q, %Q, %Q, %Q, %Q, '%q', %lld, %s, %s, %s);",
	                   path, (long long)file.st_size, (long long)file.st_mtime, m.duration,
	                   m.date, m.channels, m.bitrate, m.frequency, m.resolution,
			   m.title, m.creator, m.artist, m.genre, m.comment, m.dlna_pn,
                           m.mime, album_art, latitude, longitude, altitude);
	if( ret != SQLITE_OK )
	{
		DPRINTF(E_ERROR, L_METADATA, "Error inserting details for '%s'!\n", path);
		ret = 0;
	}
	else
	{
		ret = sqlite3_last_insert_rowid(db);
		check_for_captions(path, ret);
	}
	free_metadata(&m, free_flags);
	free(path_cpy);

	return ret;
}
