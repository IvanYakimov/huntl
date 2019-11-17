# Initialy built under debian 8 and then moved to 9
FROM ubuntu:xenial

# Prepare apt-get
RUN apt-get update -y
RUN apt-get upgrade -y
RUN apt-get install -y \
    git wget bash \
    cmake gcc \
    bzip2 m4 \
    libgmp-dev \
    python default-jdk

# Install CVC4
RUN apt-get install -y g++
RUN git clone https://github.com/CVC4/CVC4.git /cvc4
WORKDIR /cvc4
RUN ./contrib/get-antlr-3.4
RUN ./configure.sh
WORKDIR /cvc4/build
RUN make
RUN apt-get install -y python3 
RUN make check
RUN make install

# Install huntl itself
RUN apt-get install -y nano
RUN apt-get install -y llvm-3.5 clang-3.5
RUN git clone https://github.com/IvanYakimov/huntl.git /huntl
WORKDIR /huntl/build
RUN make

# Finish
WORKDIR /huntl
CMD [ "bash" ]

