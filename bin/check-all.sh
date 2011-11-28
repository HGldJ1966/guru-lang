#!/bin/bash

TIMEFORMAT=%2R

function measure()
{
  time $@ > /dev/null 2>&1
}

for f in *.g; do
  echo -n "$f:	"
  TIME=`measure guru $f 2>&1`
  RVAL=$?
  echo "$TIME / $RVAL"
done
