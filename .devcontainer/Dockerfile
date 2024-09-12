FROM ubuntu:22.04

# Install required apt packages
RUN apt update -y
RUN apt install -y \
    bash \
    git \
    curl \ 
    build-essential \
    make \
	python-is-python3 \
	time 
RUN apt update -y
RUN apt upgrade -y

# Install OPam
# RUN bash -c "sh <(curl -fsSL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)"
RUN apt install -y opam
RUN opam init -y
RUN eval $(opam env)
RUN opam update -y

RUN apt-get install -y \
    libgtksourceview-3.0-dev
# Install Coq Devdependencies
RUN opam switch create coq --packages="ocaml-variants.4.14.1+options,ocaml-option-flambda"
RUN opam init -y
RUN eval $(opam env)
RUN apt install -y libgmp-dev
RUN opam install -y \
    dune \
    ocaml-lsp-server \
    odoc \
    ocamlformat \
    utop \
    ocamlfind \
    zarith \
    lablgtk3-sourceview3
RUN opam update -y
RUN opam upgrade -y

RUN echo "export PATH=${PATH}:/workspaces/CoqPluginTutorial/coq/_build/install/default/bin" >> ~/.bashrc
RUN echo "eval $(opam env)" >> ~/.bashrc
RUN opam install -y vscoq-language-server