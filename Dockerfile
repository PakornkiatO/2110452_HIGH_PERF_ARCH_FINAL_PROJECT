FROM ubuntu:22.04

RUN apt-get update && apt-get install -y g++

WORKDIR /app
COPY main.cpp .

RUN g++ -O3 -o solver main.cpp

ENTRYPOINT ["./solver"]
