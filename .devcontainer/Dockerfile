FROM mcr.microsoft.com/devcontainers/base:noble

USER root
RUN apt-get update && apt-get install -y --no-install-recommends \
    build-essential ca-certificates curl git zstd \
    && rm -rf /var/lib/apt/lists/*

USER vscode
WORKDIR /home/vscode
SHELL ["/bin/bash", "-o", "pipefail", "-c"]

# Pin the installer; Lean itself is selected by the repository's lean-toolchain.
ARG ELAN_VERSION=v4.2.3
RUN installer_dir="$(mktemp -d)" \
    && curl --fail --location --retry 3 \
      "https://github.com/leanprover/elan/releases/download/${ELAN_VERSION}/elan-$(uname -m)-unknown-linux-gnu.tar.gz" \
      --output "${installer_dir}/elan.tar.gz" \
    && tar -xzf "${installer_dir}/elan.tar.gz" -C "${installer_dir}" \
    && "${installer_dir}/elan-init" -y --no-modify-path --default-toolchain none \
    && rm -rf "${installer_dir}"

ENV PATH="/home/vscode/.elan/bin:${PATH}"
