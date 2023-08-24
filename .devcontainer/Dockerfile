# Ubuntu 22
ARG VARIANT="jammy" 
ARG DEBIAN_FRONTEND=noninteractive
FROM mcr.microsoft.com/vscode/devcontainers/base:0-${VARIANT} as base
ENV USERNAME=vscode


# install dependencies
RUN --mount=target=/var/lib/apt/lists,type=cache,sharing=locked \
    --mount=target=/var/cache/apt,type=cache,sharing=locked \
    apt-get update && \
    apt-get -y install --no-install-recommends software-properties-common && \
    add-apt-repository -y ppa:plt/racket && \
    apt-get -y install --no-install-recommends \
    libgc-dev \
    libgmp-dev \
    racket \
    uthash-dev \
    vim

# update path
USER ${USERNAME}
WORKDIR /home/${USERNAME}
ENV PATH="/home/${USERNAME}/.local/bin:/home/${USERNAME}/.cabal/bin:/home/${USERNAME}/.ghcup/bin:$PATH"
RUN echo "export PATH=${PATH}" >> /home/${USERNAME}/.profile

# install ghcup
RUN curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | sh

ARG GHC=9.4.6
ARG CABAL=3.8.1.0
ARG STACK=2.9.3
ARG HLS=recommended

# install GHC, cabal and HLS
RUN \
    ghcup install ghc ${GHC} --set && \
    ghcup install cabal ${CABAL} --set && \
    ghcup install stack ${STACK} --set && \
    ghcup install hls ${HLS} --set

# update cabal package list
RUN cabal update

ARG RUST=1.71.0

# install rustup, rustc, and cargo
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- --default-toolchain=${RUST} -y

ADD . /home/${USERNAME}/gibbon

CMD ["bash"]
