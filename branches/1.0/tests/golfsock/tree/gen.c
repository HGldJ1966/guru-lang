#include <stdio.h>
#include <stdlib.h>

void print_nat(int n) {
  int i;
  for(i = 0; i < n; i++ ) 
    fprintf(stdout,"(s ");
  
  fprintf(stdout,"z");
  
  for(i = 0; i < n; i++ ) 
    fprintf(stdout,")");
}

void print_tree(int n) {
  if (n == 0)
    fprintf(stdout, "leaf");
  else {
    fprintf(stdout, "(((node ");
    int p = n-1;
    print_nat(p);
    fprintf(stdout, ") ");
    print_tree(p);
    fprintf(stdout, ") ");  
    print_tree(p);
    fprintf(stdout, ")");  
  }
}

int main(int argc, char **argv) {
  int n;
  int i = 1;
  int mode = 0;

  if (argc < 2) {
    fprintf(stderr,"Run with a number.\n");
    exit(1);
  }
  
  if (strcmp(argv[i],"-s") == 0) {
    mode = 1;
    i++;
    if (i == argc)
      fprintf(stderr,"Run with a number in addition to the -s flag.\n");
  }
  else if (strcmp(argv[i],"-t") == 0) {
    mode = 2;
    i++;
    if (i == argc)
      fprintf(stderr,"Run with a number in addition to the -t flag.\n");
  }

  sscanf(argv[i], "%d", &n);

  if (mode == 0) {
    // golfsock
    fprintf(stdout,"(check-term (tree ");
    print_nat(n);
    fprintf(stdout,") ");
  }
  else if (mode == 1) 
    // sc2
    fprintf(stdout,"(check ");
  else {
    // Twelf 
    fprintf(stdout,"test : (tree ");
    print_nat(n);
    fprintf(stdout,") = ");
  }

  print_tree(n);

  if (mode <= 1) // not Twelf
    fprintf(stdout,")\n");
  else
    fprintf(stdout,".\n");

  return 0;
}
