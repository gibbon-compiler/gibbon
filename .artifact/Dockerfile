# Ubuntu 22
FROM ubuntu:22.04 
ARG DEBIAN_FRONTEND=noninteractive
ENV USERNAME=root


# install dependencies
RUN apt-get update && \
    apt-get -y install --no-install-recommends software-properties-common && \
    apt-get -y install --no-install-recommends \
    libgc-dev \
    libgmp-dev \
    build-essential \
    uthash-dev \
    vim \ 
    wget \
    curl

RUN wget --no-check-certificate https://mirror.racket-lang.org/installers/7.5/racket-7.5-x86_64-linux.sh
RUN chmod +x racket-7.5-x86_64-linux.sh
RUN ./racket-7.5-x86_64-linux.sh


# update path
USER ${USERNAME}
WORKDIR /${USERNAME}
ENV PATH="/${USERNAME}/.local/bin:/${USERNAME}/.cabal/bin:/${USERNAME}/.ghcup/bin:$PATH"
RUN echo "export PATH=${PATH}" >> /${USERNAME}/.profile

#install ghcup
RUN curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | BOOTSTRAP_HASKELL_NONINTERACTIVE=1 BOOTSTRAP_HASKELL_GHC_VERSION=9.4.6 BOOTSTRAP_HASKELL_CABAL_VERSION=3.8.1.0 BOOTSTRAP_HASKELL_INSTALL_STACK=1 BOOTSTRAP_HASKELL_INSTALL_HLS=1 BOOTSTRAP_HASKELL_ADJUST_BASHRC=P sh

# update cabal package list
RUN cabal update

ARG RUST=1.71.0

# install rustup, rustc, and cargo
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y --default-toolchain=${RUST}

RUN . "$HOME/.cargo/env"

ADD . /gibbon

RUN rm /gibbon/gibbon-rts/build/gibbon_rts.h

CMD ["bash"]
