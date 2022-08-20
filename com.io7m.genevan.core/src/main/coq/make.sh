#!/bin/sh -ex

coqc -Q Genevan Genevan Genevan/ListExts.v
coqc -Q Genevan Genevan Genevan/ProtoVersion.v
coqc -Q Genevan Genevan Genevan/ProtoName.v
coqc -Q Genevan Genevan Genevan/ProtoIdentifier.v

coqc -Q Genevan Genevan Genevan/ProtoPeer/Peer.v
coqc -Q Genevan Genevan Genevan/ProtoPeer/CollectionT.v
coqc -Q Genevan Genevan Genevan/ProtoPeer/Collection.v
coqc -Q Genevan Genevan Genevan/ProtoPeer/CollectionOfProtocolsT.v
coqc -Q Genevan Genevan Genevan/ProtoPeer/CollectionOfProtocols.v
coqc -Q Genevan Genevan Genevan/ProtoPeer.v

coqc -Q Genevan Genevan Genevan/ProtoClientHandler.v
coqc -Q Genevan Genevan Genevan/ProtoServerEndpoint.v

mkdir -p html

coqdoc -Q Genevan Genevan --utf8 -d html $(find Genevan -type f -name '*.v')
