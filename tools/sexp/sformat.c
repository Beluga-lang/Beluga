/*****************************************************************************
*         A utility that formats .sexp files for human consumption.          *
*                                                                            *
*                    Authors: Francisco Ferreira                             *
*                             David Thibodeau                                *
*                                                                            *
*                                                             (c) 2015       *
*                                                                            *
*****************************************************************************/

#include <stdio.h>
#include <stdlib.h>

#define MAX (1024)
#define TAB (2)

int width(int nesting)
{
  return nesting * TAB;
}

void print (char * line, int nesting)
{
  int indent = width(nesting);
  int j;

  printf("%s\n", line);
  for(j = 0 ; j < indent ; j++) printf(" ");
}

int format(FILE * fp, int numcols)
{
  int i = 0, nesting = 0;
  char line[MAX];
  char c;

  while (fread(&c, sizeof(char), 1, fp) == 1) {

    if (c == ')') {nesting--; line[i] = c; i++;}
    else {
      if(i > 0 && line[i-1] == ')' && i + width(nesting) >= numcols) {
	line[i] = '\0';

	print(line, nesting);

	i = 0;
      }
      if (c == '(') { nesting++; line[i] = c; i++;}
      else if (!(c == ' ' && i == 0)) {
	line[i] = c; i++;
      }
    }
  }

  line[i] = '\0';
  print(line, nesting);

  return 0;
}

int main (int argc, char **argv)
{
  if (argc != 3) {
    printf("Usage: %s numcols file\n", argv[0]);
    exit(1);
  }

  int numcols = atoi(argv[1]);

  if (numcols <= 0) {
    printf("Unable to format to %d characters\n", numcols);
    exit(1);
  }

  // Hack to avoid buffer overruns
  if (numcols > (MAX / 2)) {
    printf("Unable to format to %d columns (Max is %d).\n", numcols, (MAX/2));
    exit(1);
  }

  FILE * fp = fopen(argv[2], "r");
  if (fp == NULL) {
      printf("Unable to open file: %s\n", argv[2]);
      exit(1);
    }

  int ret = format(fp, numcols);

  fclose(fp);
  return ret;
}
