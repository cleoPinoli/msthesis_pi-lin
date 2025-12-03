#!/bin/sh
exec cat `find $1 -name "*.*"` | tr -d [:space:] | wc -c
