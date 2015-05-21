#!/bin/bash
scala parsetests.scala
xargs -a trivial.txt mv -t trivialProblems/
