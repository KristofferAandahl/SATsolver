for f in UUF125.538.100/*; do
  sed -i '/^%/d' "$f"
  sed -i '/^0$/d' "$f"
done
