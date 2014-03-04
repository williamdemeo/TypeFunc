## Agda Resources

Here is a short list of Agda resources that I have found helpful (listed in the order in which I went through them).  
Most of them, and many others, can be found on the long list of references accompanying [Jan Malakovski's tutorial](http://oxij.org/note/BrutalDepTypes/).  

+ [Learn you an agda](https://github.com/williamdemeo/learn-you-an-agda), a fork of Liam O'Connor's book/tutorial (with a few corrections).
+ [A nice introductory tutorial](http://www.stephendiehl.com/posts/agda.html), by Stephen Diehl.
+ [Dependently Typed Programming in Agda](http://www.cse.chalmers.se/~ulfn/papers/afp08/tutorial.pdf), by Ulf Norell and James Chapman.

Others (that I didn't make it all the way through yet):

+ [The Agda Wiki](http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Main.HomePage).
+ [Dependent Types at Work](http://www.cse.chalmers.se/~peterd/papers/DependentTypesAtWork.pdf), by Ana Bove and Peter Dybjer. 
+ [A YouTube tutorial](http://www.youtube.com/watch?v=SQama_q9qtQ&feature=share) that uses the Level module.


## Installing Agda on Ubuntu 13.10

The following works on a generic Ubuntu 13.10 installation [1](#end-notes) (and probably others).

    sudo apt-get install agda-mode
	sudo apt-get install agda-stdlib

## End Notes

[1]: For example, I have installed and used Agda on an Amazon Web Services machine (after configuring that machine with [my startup.sh script](https://github.com/williamdemeo/dotfiles.wjd)).
