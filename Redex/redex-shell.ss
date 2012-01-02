#!/usr/bin/env mzscheme
#lang scheme

(require redex)
(require "jscore.ss")

(apply-reduction-relation*
        eval-lambdaJS-errors (term (() ,(read))))
