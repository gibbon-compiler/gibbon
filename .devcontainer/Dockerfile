# See here for image contents: https://github.com/microsoft/vscode-dev-containers/tree/v0.194.0/containers/ubuntu/.devcontainer/base.Dockerfile

# [Choice] Ubuntu version: bionic, focal
ARG VARIANT="bionic"
FROM mcr.microsoft.com/vscode/devcontainers/base:0-${VARIANT}

# [Optional] Uncomment this section to install additional OS packages.
RUN apt-get update && export DEBIAN_FRONTEND=noninteractive \
     && sudo apt-get -y install --no-install-recommends software-properties-common \
     && sudo add-apt-repository -y ppa:plt/racket \
     && sudo add-apt-repository -y ppa:hvr/ghc \
     && sudo apt-get -y install --no-install-recommends libgc-dev libgmp-dev \
     gcc-7 uthash-dev racket \
     ghc-9.0.1 cabal-install-3.4 vim
RUN curl -sSL https://get.haskellstack.org/ | sh
ENV PATH /opt/ghc/bin:/opt/cabal/bin:$PATH
RUN sudo ln -sf /usr/bin/gcc-7 /usr/bin/gcc
