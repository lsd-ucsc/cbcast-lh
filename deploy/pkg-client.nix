{ targetAddr
, mut ? true
, pkgs ? import <nixpkgs> { }
}:
pkgs.writeScript "bash-client.sh" ''
  #!${pkgs.bash}/bin/bash

  set -e -u -o pipefail
  set -x

  TMP=$(mktemp -t bash-client.XXXXXXXXXX.sh)
  trap 'rm -v "$TMP"' EXIT

  ${pkgs.python3}/bin/python ${./spit.py} '${targetAddr}' ${if mut then "--mut" else ""} > "$TMP"

  env PATH=$PATH:${pkgs.curl}/bin ${pkgs.bash}/bin/bash "$TMP"
''
