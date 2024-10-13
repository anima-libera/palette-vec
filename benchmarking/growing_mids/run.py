import subprocess, os

import config

for result_file in os.listdir("results"):
	os.remove(os.path.join("results", result_file))
os.removedirs("results")
os.makedirs("results", exist_ok=True)

for how_many_mids in range(0, 150, 2):
	command = ("cargo run --release --"
		+ f" --many-instance-count {config.many_instance_count}"
		+ f" --few-instance-count {config.few_instance_count}"
		+ f" --how-many-manies {config.how_many_manies}"
		+ f" --how-many-fews {config.how_many_fews}"
		+ f" --mid-size-min {config.mid_size_min}"
		+ f" --mid-size-max {config.mid_size_max}"
		+ f" --mid-size-step {config.mid_size_step}"
		+ f" --how-many-mids {how_many_mids}")
	results = subprocess.Popen(command, shell=True, stdout=subprocess.PIPE).stdout.read()
	with open(f"results/mids_{how_many_mids:03}", "wb") as file:
		file.write(results)
