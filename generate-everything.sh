#!/usr/bin/env sh

printf '{-# OPTIONS --prop #-}\n'
printf 'module Everything where\n\n'
find Cubical/ Gluing/ Syntax/ Multicategory/ Guarded/ \
  -type f -name "*.agda" \
  | sort \
  | sed -e 's/\//./g' -e 's/\.agda$//g' -e 's/^/import /'
