#!/bin/bash
scala -cp ".:org.sat4j.core.jar:bin/ccu.jar" src/ccu/CCURun.scala $@

