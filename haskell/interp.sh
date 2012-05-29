#!/bin/bash
if [ $# -ne 1 ]
then
  echo "Usage: `basename $0` infile.js"
  exit 65
fi

../Redex/interp-shell.ss < $1
