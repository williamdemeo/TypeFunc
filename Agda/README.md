## Installing Agda on Ubuntu 13.04

1.  Put the directory $HOME/.cabal/bin in your path:

        export PATH=$PATH:$HOME/.cabal/bin

2.  Install cabal, happy, alex, and Agda:

        sudo apt-get install cabal-install
        cabal install happy
        cabal install alex
        cabal install Agda
