# In an empty directory, save a project.godot containing "config_version=5",
# copy this file beside it, and run: godot --headless --path . --script res://godot.gd
extends SceneTree


func _initialize() -> void:
	measure.call_deferred()


func measure() -> void:
	print("Godot ", Engine.get_version_info().string)
	print("padding\trequested_width\trow_width\tcard_positions\tcard_widths\tmiddle_content_width")
	for nested in [false, true]:
		var row := HBoxContainer.new()
		row.add_theme_constant_override("separation", 0)
		root.add_child(row)
		var cards: Array[MarginContainer] = []
		var middle_content := Control.new()
		for i in 3:
			var card := MarginContainer.new()
			card.size_flags_horizontal = Control.SIZE_EXPAND_FILL
			row.add_child(card)
			cards.append(card)
			if i == 1:
				var padded := card
				if nested:
					padded = MarginContainer.new()
					card.add_child(padded)
				padded.add_theme_constant_override("margin_left", 18)
				padded.add_theme_constant_override("margin_right", 18)
				padded.add_child(middle_content)
		for width in [300, 240, 108, 107, 60, 30, 0, 300]:
			row.size = Vector2(width, 40)
			# Each nested container queues its own sort on resize.
			await process_frame
			await process_frame
			var positions := []
			var widths := []
			for card in cards:
				positions.append(card.position.x)
				widths.append(card.size.x)
			print("%s\t%d\t%s\t%s\t%s\t%s" % [
				"inner" if nested else "card", width, row.size.x, positions, widths,
				middle_content.size.x])
		row.queue_free()
	quit()
