import matplotlib.pyplot as plt
from matplotlib.colors import Normalize
import os

import config

fig, ax = plt.subplots()

color_map = plt.colormaps["rainbow"]

result_files = os.listdir("results")
result_files.sort(key=lambda name: int(name.split("_")[-1]))
color_max = len(result_files)-1

for result_file_i, result_file in enumerate(result_files):
	path = os.path.join("results", result_file)
	with open(path, "r") as file:
		lines = file.readlines()
		results = [tuple(map(int, result.split(", "))) for result in lines]
			
		def y_from_result(result):
			if result[0] == 0 and result[1] == 0:
				return 1
			elif result[0] != 0:
				return result[1] / result[0]
			else:
				raise ValueError()
		
		xs = range(0, len(results))
		ys = list(map(y_from_result, results))
		color_i = result_file_i
		color = color_map(result_file_i / color_max)
		ax.plot(xs, ys, label=path, color=color)

plt.ylim(0, 1)
plt.xlim(0, 100)

ax.set(
	xlabel="how_many_fews",
	ylabel="mem out / mem pal",
	title=("Benchmak OutPalVec vs PalVec memory usage\n"
		+ f"many_instance_count = {config.many_instance_count} "
		+ f"few_instance_count = {config.few_instance_count}"))

fig.colorbar(
	plt.cm.ScalarMappable(norm=Normalize(0, color_max), cmap=color_map),
	ax=ax,
	label="how_many_manies")

ax.grid()

fig.savefig("test.png")
plt.show()
