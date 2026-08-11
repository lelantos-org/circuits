# Native arm64 Picus image.
#
# The upstream `veridise/picus:base` is published as a single amd64 manifest, so
# `docker build https://github.com/Veridise/Picus.git` produces an image that runs under
# emulation on Apple Silicon. This rebuilds the same environment from arm64 parts.
#
# Only the z3 backend is provided — cvc4/cvc5 ship no arm64 Linux binaries — which is why
# the `picus` recipe passes `--solver z3`. circom is not installed either: the recipe
# compiles the R1CS on the host and mounts it in.
FROM --platform=linux/arm64 ubuntu:24.04

ARG PICUS_REF=main
ARG Z3_VERSION=4.13.4
# The release asset name encodes the glibc it was built against; 2.34 works on noble's 2.39.
ARG Z3_ARCHIVE=z3-4.13.4-arm64-glibc-2.34

ENV DEBIAN_FRONTEND=noninteractive

# noble/universe carries Racket 8.10 built for arm64.
RUN apt-get update \
 && apt-get install -y --no-install-recommends ca-certificates curl git racket unzip \
 && rm -rf /var/lib/apt/lists/*

# `Picus/solvers/z3` is a wrapper that execs whatever `z3` is on PATH. apt's is 4.8.12;
# this matches the 4.12/4.13 line the upstream image ships.
RUN curl -fsSL -o /tmp/z3.zip \
      "https://github.com/Z3Prover/z3/releases/download/z3-${Z3_VERSION}/${Z3_ARCHIVE}.zip" \
 && unzip -q /tmp/z3.zip -d /tmp \
 && install -m 0755 "/tmp/${Z3_ARCHIVE}/bin/z3" /usr/local/bin/z3 \
 && rm -rf /tmp/z3.zip "/tmp/${Z3_ARCHIVE}" \
 && z3 --version

RUN git clone --depth 1 --branch "${PICUS_REF}" https://github.com/Veridise/Picus.git /Picus
WORKDIR /Picus

# Dependencies declared by Picus' info.rkt.
#
# Rosette's pre-installer downloads its own Z3 and has no aarch64 Linux case, which fails
# the install outright. It skips the download when <pkg>/bin/z3 is already a symlink, so
# the install is split: unpack with --no-setup, point that symlink at the Z3 above, then
# run setup (which is when pre-installers fire).
RUN raco pkg install --auto --batch --no-setup --skip-installed rosette csv-reading graph \
 && rosette_bin="$(racket -e '(require pkg/lib) (display (pkg-directory "rosette"))')/bin" \
 && mkdir -p "$rosette_bin" \
 && ln -sf /usr/local/bin/z3 "$rosette_bin/z3" \
 && raco setup --no-docs --pkgs rosette csv-reading graph \
 && raco make picus.rkt

CMD ["/bin/bash"]
