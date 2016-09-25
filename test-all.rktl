#lang racket/load

(require "main.rkt")

(load "test-all.scm")

(when test-failed
  (exit 1))
