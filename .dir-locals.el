((coq-mode
  . ((eval .
	   (progn
	     (make-local-variable 'coq-prog-name)
             (setq coq-prog-name "hoqtop")
	     (make-local-variable 'coq-prog-args)
	     (setq coq-prog-args `("-emacs" "-indices-matter"
				  "-Q" ,(expand-file-name (locate-dominating-file buffer-file-name ".dir-locals.el")) "" )))))))
