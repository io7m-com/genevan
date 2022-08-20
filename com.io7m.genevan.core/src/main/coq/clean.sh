#!/bin/sh -ex

find Genevan -name '*.glob' -type f -exec rm -v {} \;
find Genevan -name '*.vo'   -type f -exec rm -v {} \;
find Genevan -name '*.vok'  -type f -exec rm -v {} \;
find Genevan -name '*.vos'  -type f -exec rm -v {} \;
find Genevan -name '*.aux'  -type f -exec rm -v {} \;

rm -rf html

