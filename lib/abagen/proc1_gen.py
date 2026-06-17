import os
import subprocess
import shutil
import datetime
import glob
import sys
import math

BKSIZE = [15,30,45,60,75,90,105,120,135,150]

newpath = "abalp"
if not os.path.exists(newpath):
  os.makedirs(newpath)    

goal = open(newpath + "/" + "abalp_gen.pl", "w")   

def generator(name,p):
  for bksize in BKSIZE:
    e = math.ceil(bksize * p)
    g = ":- try(10,export" + name + "abalpb(" + str(bksize) + "," + str(e) + "))."
    goal.write(g + "\n")

for i in range(1, 11):
  goal.write("% " + str(i) + "\n")
  generator("_",0.1)
  generator("_",0.2)
  generator("_",0.3)

for i in range(1, 11):
  goal.write("% " + str(i) + "\n")
  generator("_disjoint_",0.1)
  generator("_disjoint_",0.2)
  generator("_disjoint_",0.3)

for i in range(1, 11):
  goal.write("% " + str(i) + "\n")
  generator("_tabular_",0.1)
  generator("_tabular_",0.2)
  generator("_tabular_",0.3)

goal.close()

sys.exit()
