# syntax=docker/dockerfile:1
FROM ubuntu:22.04

ENV DEBIAN_FRONTEND=noninteractive PYTHONUNBUFFERED=1 PATH="/root/.cargo/bin:${PATH}"

# Install system dependencies
RUN apt-get update && apt-get install -y \
    python3 python3-pip python3-dev python3-venv git vim tmux wget curl unzip \
    libgmp-dev swig cmake autoconf gperf libboost-all-dev build-essential \
    default-jre zip pkg-config && rm -rf /var/lib/apt/lists/*

# Install Rust and Python dependencies
RUN curl https://sh.rustup.rs -sSf | bash -s -- -y
SHELL ["/bin/bash", "-c"]
RUN source $HOME/.cargo/env && \
    pip3 install --no-cache-dir --upgrade pip setuptools wheel

WORKDIR /efmc
COPY requirements.txt setup.py ./
RUN pip3 install --no-cache-dir -r requirements.txt

COPY . .
RUN pip3 install --no-cache-dir -e . && \
    pip3 install --no-cache-dir flask==2.3.3 "werkzeug>=3.0.6"

# Install CUDD and ANTLR
#RUN git clone -b 3val https://github.com/martinjonas/cudd.git && \
#    cd cudd && ./configure --enable-silent-rules --enable-obj --enable-shared && \
#    make -j$(nproc) && make install && cd .. && rm -rf cudd && \
#    mkdir -p /usr/share/java && \
#    wget -q https://www.antlr.org/download/antlr-4.11.1-complete.jar -P /usr/share/java

# Setup SMT solvers
WORKDIR /efmc/bin_solvers/
RUN python3 download.py && \
    pysmt-install --msat --yices --cvc4 --btor --picosat --bdd --confirm-agreement

WORKDIR /efmc
RUN useradd -m -u 1000 efmc && chown -R efmc:efmc /efmc
USER efmc

EXPOSE 5050
HEALTHCHECK --interval=30s --timeout=10s --start-period=5s --retries=3 \
    CMD python3 -c "import efmc" || exit 1

CMD ["python3", "-c", "print('EFMC ready. Use: efmc -h, efsmt -h, polyhorn -h')"]