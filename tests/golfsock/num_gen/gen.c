#include <stdio.h>
#include <stdlib.h>

int main(int argc, char **argv) {
  int n;
  int i = 1;
  int sc2 = 0;

  if (argc < 2) {
    fprintf(stderr,"Run with a number.\n");
    exit(1);
  }
  
  if (strcmp(argv[i],"-s") == 0) {
    sc2 = 1;
    i++;
    if (i == argc)
      fprintf(stderr,"Run with a number in addition to the -s flag.\n");
  }

  sscanf(argv[i], "%d", &n);

  if (sc2)
    fprintf(stdout,"(check ");
  else
    fprintf(stdout,"(check-term nat ");

  for(i = 0; i < n; i++ ) 
    fprintf(stdout,"(S ");

  fprintf(stdout,"Z");

  for(i = 0; i < n; i++ ) 
    fprintf(stdout,")");

  fprintf(stdout,")\n");
  return 0;
}
