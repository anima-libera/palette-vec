import subprocess, os

import config

os.makedirs("results", exist_ok=True)

for how_many_manies in range(0, 30):
	command = ("cargo run --release --"
		+ f" --how-many-manies {how_many_manies}"
		+ f" --many-instance-count {config.many_instance_count}"
		+ f" --few-instance-count {config.few_instance_count}")
	results = subprocess.Popen(command, shell=True, stdout=subprocess.PIPE).stdout.read()
	with open(f"results/manies_{how_many_manies:03}", "wb") as file:
		file.write(results)
