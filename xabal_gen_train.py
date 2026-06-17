import os
import subprocess
import shutil
import datetime
import sys
import glob

sem = ["stb", "adm", "com", "grd", "prf"]
time_limit = 60
config="configs/lazy_"
goals = glob.glob("./lib/abagen/abalp/*.bk.*.pl")
basedir = os.path.dirname(goals[0])

for s in sem:
  sdir = basedir + "/" + s
  if os.path.exists(sdir):
    shutil.rmtree(sdir)
  os.makedirs(sdir)
  for f in goals:
    cmd = "./cmdrunner \'swipl -g halt xabal.pl " + config + s + "_config.pl " + f + "\' " + str(time_limit)
    subprocess.call([cmd], shell=True)
    learnt_abaf = f.replace(".pl",".sol.aba")
    if os.path.exists(learnt_abaf):
      shutil.move(learnt_abaf, sdir + "/")
      learnt_abaf_asp = f.replace(".pl",".sol.asp")
      if os.path.exists(learnt_abaf_asp):
        shutil.move(learnt_abaf_asp, sdir + "/")
      learnt_abaf_chk = f.replace(".pl",".sol_chk.asp") 
      if os.path.exists(learnt_abaf_chk):  
        shutil.move(learnt_abaf_chk, sdir + "/")  
    else:
      with open('xabal.csv', "a") as stats:
        stats.write(datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S,"))
        stats.write(os.path.basename(f) + ",")
        stats.write(s + ",")
        stats.write("\'\\N\',")
        stats.write("\'\\N\',")
        stats.write("\'\\N\',")
        stats.write("\'\\N\',")
        stats.write("to\n")

sys.exit()