#!/bin/bash

# Change owner of mounted workspace to user
sudo chown user:user /workdir

# Install pre-commit hooks in mounted repository
cd /workdir/zephyr-model-based-testing
pre-commit install
