#!/bin/sh -ex

coqc -Q Genevan Genevan Genevan/ListExts.v
coqc -Q Genevan Genevan Genevan/ProtoVersion.v
coqc -Q Genevan Genevan Genevan/ProtoName.v
coqc -Q Genevan Genevan Genevan/ProtoIdentifier.v
coqc -Q Genevan Genevan Genevan/ProtoPeer.v
coqc -Q Genevan Genevan Genevan/ProtoClientHandler.v
coqc -Q Genevan Genevan Genevan/ProtoServerEndpoint.v

mkdir -p html

coqdoc -Q Genevan Genevan --utf8 -d html Genevan/*.v
