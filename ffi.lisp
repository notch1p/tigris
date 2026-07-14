(defun %println (x) 
  (declare (optimize (speed 3) (debug 0) (safety 0)))
  (format t "~A~%" x))

(defun %string-append (s1 s2) 
  (declare (optimize (speed 3) (debug 0) (safety 0)))
  (concatenate 'string s1 s2))

(defun %to-string (s) 
  (declare (optimize (speed 3) (debug 0) (safety 0)))
  (format nil "~A" s))

(defun %read (_) (declare (ignore _)) (read))