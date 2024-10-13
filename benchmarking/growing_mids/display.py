import matplotlib.pyplot as plt
from matplotlib.colors import Normalize
import os

import config

fig, ax = plt.subplots()

color_map = plt.colormaps["rainbow"]

result_files = os.listdir("results")
result_files.sort(key=lambda name: int(name.split("_")[-1]))
color_min = int(result_files[0].split("_")[-1])
color_max = int(result_files[-1].split("_")[-1])

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

		xs = [
			config.mid_size_min + result_i * config.mid_size_step
			for result_i in range(0, len(results))]
		ys = list(map(y_from_result, results))
		color_i = int(result_files[result_file_i].split("_")[-1])
		color = color_map(color_i / color_max)
		ax.plot(xs, ys, label=path, color=color)

plt.ylim(0, 1.01)
plt.xlim(config.mid_size_min, config.mid_size_max)

ax.set(
	xlabel="mid_instance_count",
	ylabel="mem out / mem pal",
	title=("Benchmak OutPalVec vs PalVec memory usage\n"
		+ f"many_instance_count = {config.many_instance_count} "
		+ f"few_instance_count = {config.few_instance_count}\n"
		+ f"how_many_manies = {config.how_many_manies} "
		+ f"how_many_fews = {config.how_many_fews}"))

fig.colorbar(
	plt.cm.ScalarMappable(norm=Normalize(color_min, color_max), cmap=color_map),
	ax=ax,
	label="how_many_mids")

ax.grid()

fig.savefig("test.png")
plt.show()
