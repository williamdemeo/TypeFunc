## Agda Resources

Here is a short list of Agda resources that I have found helpful.  Most of them, and many others, can be found
on the long list of references accompanying [Jan Malakovski's tutorial](http://oxij.org/note/BrutalDepTypes/).

+ [A nice introductory tutorial](http://www.stephendiehl.com/posts/agda.html), by Stephen Diehl.
+ [Learn you an agda](https://github.com/williamdemeo/learn-you-an-agda), a fork of Liam O'Connor's book/tutorial (with a few corrections).
+ [A YouTube tutorial](http://www.youtube.com/watch?v=SQama_q9qtQ&feature=share) that uses the Level module.
+ [The Agda Wiki](http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Main.HomePage).


## Installing Agda on Ubuntu 13.10

The following works on a generic[^1] Ubuntu 13.10 installation (and probably others).

    sudo apt-get install agda-mode
	sudo apt-get install agda-stdlib

### Alternatively...

1.  Put the directory $HOME/.cabal/bin in your path; e.g., put the following
    line in your $HOME/.profile file:

        export PATH=$PATH:$HOME/.cabal/bin

2.  Install cabal, happy, alex, and Agda:

        sudo apt-get install cabal-install
        cabal install happy
        cabal install alex
        cabal install Agda


## Notes

[^1]: For example, I have installed and used Agda on an Amazon Web Services machine (after configuring that machine with [my startup.sh script](https://github.com/williamdemeo/dotfiles.wjd)).
