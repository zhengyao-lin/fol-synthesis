FROM python:3.9-slim-buster

RUN apt-get update && \
    apt-get install -y git-core bash && \
    rm -rf /var/cache/apt/archives /var/lib/apt/lists/*

WORKDIR /opt/synthesis

ADD requirements.txt /opt/synthesis
RUN python3 -m pip install --no-cache-dir -r requirements.txt

ADD synthesis /opt/synthesis/synthesis
ADD evaluations /opt/synthesis/evaluations
ADD vampire /opt/synthesis/vampire

RUN echo "PS1='\\$ '" >> ~/.bashrc && \
    echo "cat << EOT" >> ~/.bashrc && \
    echo >> ~/.bashrc && \
    echo "    Welcome to the artifact image of the paper" >> ~/.bashrc && \
    echo "        \033[1mSynthesizing Axiomatizations using Logic Learning\033[0m" >> ~/.bashrc && \
    echo "        Paul Krogmeier, Zhengyao Lin, Adithya Murali, P. Madhusudan" >> ~/.bashrc && \
    echo >> ~/.bashrc && \
    echo "    Alongside this image you should find a README.md file which contains instructions to use this image." >> ~/.bashrc && \
    echo "    If not, try visiting this URL: \033[4mhttps://github.com/rod-lin/fol-synthesis/tree/oopsla22\033[0m" >> ~/.bashrc && \
    echo >> ~/.bashrc && \
    echo "EOT" >> ~/.bashrc

ENTRYPOINT bash
