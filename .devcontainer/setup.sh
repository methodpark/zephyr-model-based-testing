while [ "$(find /home/user -type f -name 'tla2tools.jar')" == "" ]; do
	sleep 3;
done

sudo chown user:user /workdir

ln -s $(find /home/user/ -type f -name 'tla2tools.jar' -print -quit 2>/dev/null) /home/user/tla2tools.jar
cd /workdir/zephyr-mmodel-based-testing
pre-commit install
