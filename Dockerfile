FROM debian:bookworm-slim AS build
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates curl zstd && rm -rf /var/lib/apt/lists/*
WORKDIR /src
COPY lean-toolchain .
RUN version="$(sed 's/^leanprover\/lean4:v//;s/\r$//' lean-toolchain)" && \
    curl -fsSL --retry 3 "https://github.com/leanprover/lean4/releases/download/v${version}/lean-${version}-linux.tar.zst" -o /tmp/lean.tar.zst && \
    mkdir /opt/lean && tar --zstd -xf /tmp/lean.tar.zst -C /opt/lean --strip-components=1 && rm /tmp/lean.tar.zst
ENV PATH="/opt/lean/bin:${PATH}"
COPY lakefile.toml Main.lean Leaf.lean ./
COPY Leaf/ Leaf/
RUN lake build leaf

FROM debian:bookworm-slim
RUN apt-get update && apt-get install -y --no-install-recommends libgmp10 libstdc++6 libuv1 && rm -rf /var/lib/apt/lists/*
WORKDIR /app
COPY --from=build /src/.lake/build/bin/leaf /app/leaf
RUN mkdir data && chown nobody:nogroup data
USER nobody
ENV PORT=10000
CMD ["/app/leaf"]
