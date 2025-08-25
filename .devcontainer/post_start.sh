#! /bin/bash
# fixing the symlink for tla2tools if it is broken. This can occur when the
# vscode tla extension is updated
if  file /home/user/tla2tools.jar | grep broken 2>&1>/dev/null; then
  ln -sf $(find /home/user/ -type f -name "tla2tools.jar" -print -quit) /home/user/tla2tools.jar;
fi
