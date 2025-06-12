#!/bin/sh
( echo "{-# LINE 1 \"$1\" #-}" ; sed -e 's/--[XW]//' $2 ) > $3
