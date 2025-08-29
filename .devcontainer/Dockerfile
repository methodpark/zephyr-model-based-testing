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

# Install most recent version of the TLA+ tools and Community Modules
ARG TLA_TOOLS_JAR_URL=https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar
ARG TLA_COMMUNITY_MODULES_JAR_URL=https://github.com/tlaplus/CommunityModules/releases/latest/download/CommunityModules-deps.jar
RUN wget -O /usr/share/java/tla2tools.jar ${TLA_TOOLS_JAR_URL} && \
    wget -O /usr/share/java/CommunityModules-deps.jar ${TLA_COMMUNITY_MODULES_JAR_URL}

# Add TLA+ tools, community modules and our TLA+ library to the Java classpath
ENV CLASSPATH=/usr/share/java/tla2tools.jar:/usr/share/java/CommunityModules-deps.jar:/workdir/zephyr-model-based-testing/specs/lib

USER user
COPY .bash_aliases /home/user/.bash_aliases
