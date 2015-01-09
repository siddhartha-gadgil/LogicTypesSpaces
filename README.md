LogicTypesSpaces
================

Mostly Agda code for a course and blog on "Logic, Types and Spaces"


###Getting Agda:

####For Ubuntu 64-Bit: 

- Open your terminal and run the following commands
``` shell
sudo apt-get install emacs libgmp-dev zlib1g-dev libncurses5-dev
wget http://bit.ly/1xKVN5u  #This file will take a little while to download (195MB).
cd \
sudo tar xvf ~/haskell-platform-2014.2.0.0-unknown-linux-x86_64.tar.gz
sudo /usr/local/haskell/ghc-7.8.3-x86-64/bin/activate-hs
cabal update
cabal install alex
cabal install happy
cabal install cpphs
sudo cabal install --global Agda
agda-mode setup
agda-mode compile
```

----

A short [Tutorial](https://github.com/guillaumebrunerie/HoTT/blob/master/Agda/tutorial/README.md#emacs-mode) for Agda development in Emacs


####Some Agda commands in Emacs

Keybinding                      | Description
--------------------------------|---------------------------------
<kbd>ctrl-c ctrl-l</kbd>        | Load File
<kbd>ctrl-c ctrl-x ctrl-c</kbd> | Compile File
<kbd>ctrl-c ctrl-x ctrl-q</kbd> | Quit Agda mode
<kbd>ctrl-c ctrl-x ctrl-r</kbd> | Kill and Restart Agda
<kbd>ctrl-c ctrl-c</kbd>        | Case split
<kbd>ctrl-c ctrl-r</kbd>        | Refine goal
<kbd>ctrl-c ctrl-f</kbd>        | Next goal
<kbd>ctrl-c ctrl-b</kbd>        | Previous goal
<kbd>ctrl-c ctrl-n</kbd>        | Evaluate an expression
<kbd>ctrl-c ctrl-d</kbd>        | Infer (Deduce) type




