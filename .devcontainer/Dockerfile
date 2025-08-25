FROM ghcr.io/zephyrproject-rtos/zephyr-build:v0.27.4

USER root

RUN apt-get update && \
    apt-get upgrade -y && \
    apt-get install -y vim bash-completion && \
    apt-get install -y openjdk-17-jre  # required for TLA+

RUN pip install pre-commit

RUN mkdir -p /workdir/zephyr-model-based-testing
RUN chown user:user /workdir
RUN chsh -s /bin/bash user

USER user

ENV TLA_TOOLS_JAR=/home/user/tla2tools.jar
COPY .bash_aliases /home/user/.bash_aliases
