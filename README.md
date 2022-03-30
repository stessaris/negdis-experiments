# Code and experiments for the paper "Process discovery on deviant traces and other stranger things"

This repository include the data and the support code to run the experiments, as well as the code implementing the algorithm described in the paper (in the [dist](dist) directory).

## Running the experiments

The experiments should be run using [Jupyter](https://jupyter.org/), either using its web based interface or [nbconvert](https://nbconvert.readthedocs.io/en/latest/). The required software can be installed using [Anaconda](https://www.anaconda.com/) Python distribution or manually installing the [clingo](https://potassco.org/clingo/) ASP solver (version *5.4.0* must used!). We strongly suggest the former because it's easier to ensure a reproducible environment via virtual environments. The required conda packages are listed in the `binder/environment.yml` file (on Windows the `environment.win.yml` file must be used instead).

Below you'll find specific instructions for different options to set-up the Jupyter working environment, once the environment is running you can just open the `run_*_experiments.ipynb` and run every cell. Alternatively, on Linux or OSX, you can open a command line terminal with the right *conda environment* and run the command:

``` bash
jupyter nbconvert --ExecutePreprocessor.timeout=-1 --to html --execute run_*_experiments.ipynb
```

that executes all the notebooks and saves their output in separate HTML document (on Windows the command line might need to be adapted).

The raw data generated by the experiments will be available in the [results](results) directory.

### Run locally

Assuming that *Anaconda* or *Miniconda* are already installed you can just create the virtual environment and start *Jupyter* (or use the *nbconvert* workflow without starting the server):

``` bash
conda env create -f=binder/environment.yml
conda activate negdis
jupyter lab
```

### Using Binder

The repository is compatible with [Binder](https://mybinder.org/) and [repo2docker](http://repo2docker.readthedocs.io/). To use *repo2docker* on the local machine you can use the command `jupyter-repo2docker` with the path of the cloned repository or its URL. E.g.:

``` bash
jupyter-repo2docker .
```

which starts a container with *Jupyter* that can be accessed via web browser.

Using both these methods the filesystem of the container will be separated from the one on the host, so the results must be exported using the Jupyter interface. *Jupyter* enables the use of a command line terminal that can be used for *nbconvert*.

### Using Docker

You can also use [Docker](https://www.docker.com/) with a *Jupyter* image, it's similar to the *Binder* option, but you could mount the local filesystem on the container, so you don't need to copy the results afterwards. First you need to start a container with *Jupyter* that can access the local directory:

``` bash
docker run --rm -p 8888:8888 -v "$PWD":/home/jovyan/work jupyter/minimal-notebook
```

The local directory will be available in the `work` directory within the *Jupyter* interface. Then you need to install the required packages opening a terminal (within the *Jupyter* interface) and run the command:

``` bash
conda env update -n=base  -f=work/binder/environment.yml
```

For details see [Jupyter Docker Stacks - Running a Container](https://jupyter-docker-stacks.readthedocs.io/en/latest/using/running.html). The `-v` option mounts the current directory on the virtual machine, so the results of the experiments will be stored on the local filesystem.

## Available experiments

Due to missing distribution rights for the *CERV* dataset, the files with the event logs might not be included in this repository. Please get in touch with the authors for more details.

### ASPrin optimisation experiments

- [run_asprin_cerv_experiments](run_asprin_cerv_experiments.ipynb): *CERV* dataset
- [run_asprin_dreyers_experiments](run_asprin_dreyers_experiments.ipynb): [Dreyers dataset](https://github.com/tslaats/EventLogs)

### Experiments presented in [Process discovery on deviant traces and other stranger things](https://doi.org/10.48550/arXiv.2109.14883)

- [run_cerv_experiments](run_cerv_experiments.ipynb): *CERV* dataset
- [run_reallife_experiments](run_reallife_experiments.ipynb)
- [run_synt_experiments](run_synt_experiments.ipynb)
