FROM python:3.9-slim-buster

RUN apt-get update && \
    apt-get install -y git-core bash && \
    rm -rf /var/cache/apt/archives /var/lib/apt/lists/*

ADD synthesis /opt/synthesis/synthesis
ADD evaluations /opt/synthesis/evaluations
ADD vampire /opt/synthesis/vampire
ADD requirements.txt /opt/synthesis

WORKDIR /opt/synthesis

RUN python3 -m pip install --no-cache-dir -r requirements.txt

ENTRYPOINT bash
