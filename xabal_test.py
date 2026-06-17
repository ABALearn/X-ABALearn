import os
import subprocess
import shutil
import datetime
import glob

sem = ["stb", "adm", "com", "prf", "grd"]
csv = ["acute", "autism", "breastw", "krkp", "mushroom", "voting" ]
config="configs/aamas2025_"
basedir="xabal/"

for c in csv:
  for s in sem:
    for i in range(1, 6):
      learnt_abaf = basedir + c + ".csv.f" + str(i) + ".bk.sol." + s
      if os.path.exists(learnt_abaf + ".aba"):
        print(learnt_abaf)
        test_cmd = "swipl -g listing\\(lopt/1\\) -g test\\(\\'" + learnt_abaf + "\\'\\) -g halt xabal.pl " + config + s + "_config.pl xabal/" + c + ".csv.f" + str(i) + ".pl"
        subprocess.call([test_cmd], shell=True)

pm_cmd = "swipl -g pm -g halt performance_eval.pl"
subprocess.call([pm_cmd], shell=True)

newpath = basedir + "PM"
if not os.path.exists(newpath):
  os.makedirs(newpath)

pattern = "*.PM.csv"
files_to_move = glob.glob(basedir + pattern)
for file in files_to_move:
  file_name = os.path.basename(file)
  shutil.move(file, basedir + "PM/" + file_name)

for c in csv:
  c_pm_file = open(basedir + "PM/" + c + ".PM.csv", "w")
  for s in sem:
    pm_filename = basedir + "PM/" + c + "." + s + ".PM.csv"
    pm_file = open(pm_filename, "r")
    if os.path.exists(pm_filename):
      c_pm_file.write(">>> " + s + " <<<\n\n")
      shutil.copyfileobj(pm_file, c_pm_file)
      c_pm_file.write("\n")
  c_pm_file.close()
