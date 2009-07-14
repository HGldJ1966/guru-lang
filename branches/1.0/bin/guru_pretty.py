#!/usr/bin/python
"""Guru Pretty Printer

Converts guru strings into actual strings
using data from standard out.

Usage:
guru myfile.g | ./guru-pretty.py

Maintainer: Derek Bruce (dbruce@gmail.com)
"""

import sys
import re


chars = {
('ff', 'ff', 'ff', 'ff', 'ff', 'ff', 'ff'): " ",
('tt', 'ff', 'ff', 'ff', 'ff', 'ff', 'ff'): " ",
('ff', 'tt', 'ff', 'ff', 'ff', 'ff', 'ff'): " ",
('tt', 'tt', 'ff', 'ff', 'ff', 'ff', 'ff'): " ",
('ff', 'ff', 'tt', 'ff', 'ff', 'ff', 'ff'): " ",
('tt', 'ff', 'tt', 'ff', 'ff', 'ff', 'ff'): " ",
('ff', 'tt', 'tt', 'ff', 'ff', 'ff', 'ff'): " ",
('tt', 'tt', 'tt', 'ff', 'ff', 'ff', 'ff'): " ",
('ff', 'ff', 'ff', 'tt', 'ff', 'ff', 'ff'): " ",
('tt', 'ff', 'ff', 'tt', 'ff', 'ff', 'ff'): " ",
('ff', 'tt', 'ff', 'tt', 'ff', 'ff', 'ff'): " ",
('tt', 'tt', 'ff', 'tt', 'ff', 'ff', 'ff'): " ",
('ff', 'ff', 'tt', 'tt', 'ff', 'ff', 'ff'): " ",
('tt', 'ff', 'tt', 'tt', 'ff', 'ff', 'ff'): "\r",
('ff', 'tt', 'tt', 'tt', 'ff', 'ff', 'ff'): " ",
('tt', 'tt', 'tt', 'tt', 'ff', 'ff', 'ff'): " ",
('ff', 'ff', 'ff', 'ff', 'tt', 'ff', 'ff'): " ",
('tt', 'ff', 'ff', 'ff', 'tt', 'ff', 'ff'): " ", 
('ff', 'tt', 'ff', 'ff', 'tt', 'ff', 'ff'): " ", 
('tt', 'tt', 'ff', 'ff', 'tt', 'ff', 'ff'): " ", 
('ff', 'ff', 'tt', 'ff', 'tt', 'ff', 'ff'): " ", 
('tt', 'ff', 'tt', 'ff', 'tt', 'ff', 'ff'): " ", 
('ff', 'tt', 'tt', 'ff', 'tt', 'ff', 'ff'): " ", 
('tt', 'tt', 'tt', 'ff', 'tt', 'ff', 'ff'): " ", 
('ff', 'ff', 'ff', 'tt', 'tt', 'ff', 'ff'): " ", 
('tt', 'ff', 'ff', 'tt', 'tt', 'ff', 'ff'): " ", 
('ff', 'tt', 'ff', 'tt', 'tt', 'ff', 'ff'): " ", 
('tt', 'tt', 'ff', 'tt', 'tt', 'ff', 'ff'): " ", 
('ff', 'ff', 'tt', 'tt', 'tt', 'ff', 'ff'): " ", 
('tt', 'ff', 'tt', 'tt', 'tt', 'ff', 'ff'): " ", 
('ff', 'tt', 'tt', 'tt', 'tt', 'ff', 'ff'): " ", 
('tt', 'tt', 'tt', 'tt', 'tt', 'ff', 'ff'): " ",
('ff', 'ff', 'ff', 'ff', 'ff', 'tt', 'ff'): " ",
('tt', 'ff', 'ff', 'ff', 'ff', 'tt', 'ff'): "!",
('ff', 'tt', 'ff', 'ff', 'ff', 'tt', 'ff'): "\"",
('tt', 'tt', 'ff', 'ff', 'ff', 'tt', 'ff'): "#",
('ff', 'ff', 'tt', 'ff', 'ff', 'tt', 'ff'): "$",
('tt', 'ff', 'tt', 'ff', 'ff', 'tt', 'ff'): "%",
('ff', 'tt', 'tt', 'ff', 'ff', 'tt', 'ff'): "&",
('tt', 'tt', 'tt', 'ff', 'ff', 'tt', 'ff'): "'",
('ff', 'ff', 'ff', 'tt', 'ff', 'tt', 'ff'): "(",
('tt', 'ff', 'ff', 'tt', 'ff', 'tt', 'ff'): ")",
('ff', 'tt', 'ff', 'tt', 'ff', 'tt', 'ff'): "*",
('tt', 'tt', 'ff', 'tt', 'ff', 'tt', 'ff'): "+",
('ff', 'ff', 'tt', 'tt', 'ff', 'tt', 'ff'): ",",
('tt', 'ff', 'tt', 'tt', 'ff', 'tt', 'ff'): "-",
('ff', 'tt', 'tt', 'tt', 'ff', 'tt', 'ff'): ".",
('tt', 'tt', 'tt', 'tt', 'ff', 'tt', 'ff'): "/",
('ff', 'ff', 'ff', 'ff', 'tt', 'tt', 'ff'): "0",
('tt', 'ff', 'ff', 'ff', 'tt', 'tt', 'ff'): "1",
('ff', 'tt', 'ff', 'ff', 'tt', 'tt', 'ff'): "2",
('tt', 'tt', 'ff', 'ff', 'tt', 'tt', 'ff'): "3",
('ff', 'ff', 'tt', 'ff', 'tt', 'tt', 'ff'): "4",
('tt', 'ff', 'tt', 'ff', 'tt', 'tt', 'ff'): "5",
('ff', 'tt', 'tt', 'ff', 'tt', 'tt', 'ff'): "6",
('tt', 'tt', 'tt', 'ff', 'tt', 'tt', 'ff'): "7",
('ff', 'ff', 'ff', 'tt', 'tt', 'tt', 'ff'): "8",
('tt', 'ff', 'ff', 'tt', 'tt', 'tt', 'ff'): "9",
('ff', 'tt', 'ff', 'tt', 'tt', 'tt', 'ff'): ":",
('tt', 'tt', 'ff', 'tt', 'tt', 'tt', 'ff'): ";",
('ff', 'ff', 'tt', 'tt', 'tt', 'tt', 'ff'): "<",
('tt', 'ff', 'tt', 'tt', 'tt', 'tt', 'ff'): "=",
('ff', 'tt', 'tt', 'tt', 'tt', 'tt', 'ff'): ">",
('tt', 'tt', 'tt', 'tt', 'tt', 'tt', 'ff'): "?",
('ff', 'ff', 'ff', 'ff', 'ff', 'ff', 'tt'): "@",
('tt', 'ff', 'ff', 'ff', 'ff', 'ff', 'tt'): "A",
('ff', 'tt', 'ff', 'ff', 'ff', 'ff', 'tt'): "B",
('tt', 'tt', 'ff', 'ff', 'ff', 'ff', 'tt'): "C",
('ff', 'ff', 'tt', 'ff', 'ff', 'ff', 'tt'): "D",
('tt', 'ff', 'tt', 'ff', 'ff', 'ff', 'tt'): "E",
('ff', 'tt', 'tt', 'ff', 'ff', 'ff', 'tt'): "F",
('tt', 'tt', 'tt', 'ff', 'ff', 'ff', 'tt'): "G",
('ff', 'ff', 'ff', 'tt', 'ff', 'ff', 'tt'): "H",
('tt', 'ff', 'ff', 'tt', 'ff', 'ff', 'tt'): "I",
('ff', 'tt', 'ff', 'tt', 'ff', 'ff', 'tt'): "J",
('tt', 'tt', 'ff', 'tt', 'ff', 'ff', 'tt'): "K",
('ff', 'ff', 'tt', 'tt', 'ff', 'ff', 'tt'): "L",
('tt', 'ff', 'tt', 'tt', 'ff', 'ff', 'tt'): "M",
('ff', 'tt', 'tt', 'tt', 'ff', 'ff', 'tt'): "N",
('tt', 'tt', 'tt', 'tt', 'ff', 'ff', 'tt'): "O",
('ff', 'ff', 'ff', 'ff', 'tt', 'ff', 'tt'): "P",
('tt', 'ff', 'ff', 'ff', 'tt', 'ff', 'tt'): "Q",
('ff', 'tt', 'ff', 'ff', 'tt', 'ff', 'tt'): "R",
('tt', 'tt', 'ff', 'ff', 'tt', 'ff', 'tt'): "S",
('ff', 'ff', 'tt', 'ff', 'tt', 'ff', 'tt'): "T",
('tt', 'ff', 'tt', 'ff', 'tt', 'ff', 'tt'): "U",
('ff', 'tt', 'tt', 'ff', 'tt', 'ff', 'tt'): "V",
('tt', 'tt', 'tt', 'ff', 'tt', 'ff', 'tt'): "W",
('ff', 'ff', 'ff', 'tt', 'tt', 'ff', 'tt'): "X",
('tt', 'ff', 'ff', 'tt', 'tt', 'ff', 'tt'): "Y",
('ff', 'tt', 'ff', 'tt', 'tt', 'ff', 'tt'): "Z",
('tt', 'tt', 'ff', 'tt', 'tt', 'ff', 'tt'): "[",
('ff', 'ff', 'tt', 'tt', 'tt', 'ff', 'tt'): "\\",
('tt', 'ff', 'tt', 'tt', 'tt', 'ff', 'tt'): "]",
('ff', 'tt', 'tt', 'tt', 'tt', 'ff', 'tt'): "^",
('tt', 'tt', 'tt', 'tt', 'tt', 'ff', 'tt'): "_",
('ff', 'ff', 'ff', 'ff', 'ff', 'tt', 'tt'): "`",
('tt', 'ff', 'ff', 'ff', 'ff', 'tt', 'tt'): "a",
('ff', 'tt', 'ff', 'ff', 'ff', 'tt', 'tt'): "b",
('tt', 'tt', 'ff', 'ff', 'ff', 'tt', 'tt'): "c",
('ff', 'ff', 'tt', 'ff', 'ff', 'tt', 'tt'): "d",
('tt', 'ff', 'tt', 'ff', 'ff', 'tt', 'tt'): "e",
('ff', 'tt', 'tt', 'ff', 'ff', 'tt', 'tt'): "f",
('tt', 'tt', 'tt', 'ff', 'ff', 'tt', 'tt'): "g",
('ff', 'ff', 'ff', 'tt', 'ff', 'tt', 'tt'): "h",
('tt', 'ff', 'ff', 'tt', 'ff', 'tt', 'tt'): "i",
('ff', 'tt', 'ff', 'tt', 'ff', 'tt', 'tt'): "j",
('tt', 'tt', 'ff', 'tt', 'ff', 'tt', 'tt'): "k",
('ff', 'ff', 'tt', 'tt', 'ff', 'tt', 'tt'): "l",
('tt', 'ff', 'tt', 'tt', 'ff', 'tt', 'tt'): "m",
('ff', 'tt', 'tt', 'tt', 'ff', 'tt', 'tt'): "n",
('tt', 'tt', 'tt', 'tt', 'ff', 'tt', 'tt'): "o",
('ff', 'ff', 'ff', 'ff', 'tt', 'tt', 'tt'): "p",
('tt', 'ff', 'ff', 'ff', 'tt', 'tt', 'tt'): "q",
('ff', 'tt', 'ff', 'ff', 'tt', 'tt', 'tt'): "r",
('tt', 'tt', 'ff', 'ff', 'tt', 'tt', 'tt'): "s",
('ff', 'ff', 'tt', 'ff', 'tt', 'tt', 'tt'): "t",
('tt', 'ff', 'tt', 'ff', 'tt', 'tt', 'tt'): "u",
('ff', 'tt', 'tt', 'ff', 'tt', 'tt', 'tt'): "v",
('tt', 'tt', 'tt', 'ff', 'tt', 'tt', 'tt'): "w",
('ff', 'ff', 'ff', 'tt', 'tt', 'tt', 'tt'): "x",
('tt', 'ff', 'ff', 'tt', 'tt', 'tt', 'tt'): "y",
('ff', 'tt', 'ff', 'tt', 'tt', 'tt', 'tt'): "z",
('tt', 'tt', 'ff', 'tt', 'tt', 'tt', 'tt'): "{",
('ff', 'ff', 'tt', 'tt', 'tt', 'tt', 'tt'): "|",
('tt', 'ff', 'tt', 'tt', 'tt', 'tt', 'tt'): "}",
('ff', 'tt', 'tt', 'tt', 'tt', 'tt', 'tt'): "~",
('tt', 'tt', 'tt', 'tt', 'tt', 'tt', 'tt'): " "
}

class guru_parser:
  """Parses guru lang into a pretty format."""
  def guru_parser(self):
    pass
  def parse_gstring(self, str):
#    str = str.replace(' ', ''): " ",replace('\t', '')
    self.compiled_char = re.compile('\(u?cons \(vecc ([ft]+) \(vecc ([ft]+) \(vecc ([ft]+) \(vecc ([ft]+) \(vecc ([ft]+) \(vecc ([ft]+) \(vecc ([ft]+)')
    match = self.compiled_char.findall(str)
    final_string = ''
    if (match):
      for g in match:
        #print g
        final_string = final_string + chars[g]
      print final_string
    else:
      print "Could not find string:"
      print str
  def parse_unat(self, str):
    str = str.replace(' ', '')
    print str.count("(S")

def main():
  gparser = guru_parser()
  #gparser.parse_gstring("(cons (vecc ff (vecc tt (vecc tt (vecc tt (vecc tt (vecc tt (vecc tt")
  while 1:
    line = sys.stdin.readline()
    if line == '' or line[0:8] == "Trusting":
      break
    gparser.parse_gstring(line)

if __name__ == "__main__":
  main()

