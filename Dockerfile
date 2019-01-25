
# Use the big image from the bintree benchmark as our base.
# Thus you must build that first:
FROM bintree-bench
#FROM fpco/stack-build:lts-12.25

RUN apt-get update && apt-get install -y valgrind

# Cache Gibbon build and test dependencies in the container
WORKDIR /trees
COPY ./gibbon-compiler/stack.yaml ./gibbon-compiler/gibbon.cabal /trees/gibbon-compiler/
RUN cd /trees/gibbon-compiler/ && stack build gibbon --flag gibbon:llvm_enabled --only-dependencies

ADD . /trees

RUN cd /trees && DOCKER=1 LLVM_ENABLED=1 ./run_all_tests.sh
