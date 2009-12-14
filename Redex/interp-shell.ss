#!/usr/bin/env mzscheme
#lang scheme

(require "interp.ss")

; Suppresses printing the result (which is invariably undefined)
(void ((interp empty-env) (read)))