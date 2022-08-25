Synthesizing Axiomatizations using Logic Learning
---

Welcome! This document describes how to perform the evaluations in the OOPSLA 22 paper
*Synthesizing Axiomatizations using Logic Learning*.

In the following sections, we will first introduce how to set up the environment to
run this artifact (Getting Started Guide), and then give instructions to run each
of the experiements in the paper (Step-by-Step Instructions).


## Getting Started Guide

This artifact is packaged in a Docker image that can be found alongside this documentation with the name `image.tar.gz`.
To load this image, first install Docker following the instructions at [https://docs.docker.com/engine/install/](https://docs.docker.com/engine/install/).
As another prerequisite, [`gzip`](https://www.gnu.org/software/gzip/) should also be installed in order to decompress the image.

After these required software are installed, run the following command to load the Docker image:
```
$ gunzip -c <path to image.tar.gz> | docker load
Loaded image ID: <image ID>
```

Now run the image to start the artifact:
```
$ docker run -it <image ID>
```

Once inside the container, follow the instructions in the next section to run the experiments.

## Step-by-Step Instructions

Our paper evaluates results of 4 experiments:
1. (Section 5.3) Synthesizing modal axioms for 17 modal logics (using constraint solving)
2. (Section 5.3.3) Same as 1 but using enumeration
3. (Section 6.3) Synthesizing equational axioms for language structures (using constraint solving)
4. (Section 6.3.3) Same as 3 but using enumeration

We have put together a Bash script to run all 4 experiments:
```
$ evaluations/run_all.sh
```

Note that this script will take a long time.
On a machine with a 20-core Intel Core i7-12700K CPU and 32 GB of memory,
the experiments took the following amounts of time to finish.
- Experiment 1: around 10 minutes
- Experiment 2: around 20 minutes
- Experiment 3: around 30 minutes
- Experiment 4: around 24 hours

You can also comment out relevant part of the script to skip certain experiment.

At the end of each experiment, the script will print a command to show the results in a more readable form.
For example, for experiment 1, the script prints:
```
Evaluation 1. Synthesizing modal axioms for 17 modal logics (using constraint solving).
    Results are saved to eval_results/modal-smt-results.pickle.
    Running with 17 parallel jobs.
    Took: ...
To show the results: python3 -m evaluations.modal show eval_results/modal-smt-results.pickle
```
Then you can run
```
$ python3 -m evaluations.modal show eval_results/modal-smt-results.pickle
```
to show the detailed results of experiment 1, including the time taken for each component in the synthesis algorithm,
and time at which each candidate axiom was synthesized.
