# FROM ubuntu:22.04

# RUN apt-get update && apt-get install -y g++

# WORKDIR /app
# COPY main.cpp .

# RUN g++ -O3 -o solver main.cpp

# ENTRYPOINT ["./solver"]

# ── Stage 1: Build ──────────────────────────────────────────────────────────
FROM --platform=linux/amd64 gcc:13 AS builder

WORKDIR /app

COPY main_optimized.cpp .

RUN g++ -O3 -march=znver1 -std=c++17 -pthread -o solver main_optimized.cpp

# ── Stage 2: Runtime (same base as builder to avoid GLIBCXX version mismatch) ─
FROM --platform=linux/amd64 gcc:13

WORKDIR /app

COPY --from=builder /app/solver .

ENTRYPOINT ["./solver"]