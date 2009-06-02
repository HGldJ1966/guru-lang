ggetc_t gnext_char(gstdin_t in) {
  char c = fgetc_unlocked(stdin);
  if (c == EOF)  
    return ggetc_none(type_name_gstdin_t, in);
  else
    return ggetc_char(type_name_gstdin_t, c & 127, in);
}

