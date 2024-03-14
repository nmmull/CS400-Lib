FROM haskell:8

RUN cabal update
RUN cabal install Agda

RUN mkdir /root/.agda
RUN touch /root/.agda/libraries
RUN touch /root/.agda/defaults
RUN echo "/workspaces/CS400-Lib/cs400-lib.agda-lib" > /root/.agda/libraries
RUN echo "cs400-lib" > /root/.agda/defaults

WORKDIR /home
