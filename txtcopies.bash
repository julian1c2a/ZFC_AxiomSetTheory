#!/bin/bash

# Directorio de origen y destino
ORIGEN="./ZFCAxiomSetTheory"
DESTINO="./txtcopies"

# 1. Crear el directorio de destino si no existe.
# El flag -p evita errores si el directorio ya existe.
echo "Creando el directorio de destino en '$DESTINO'..."
mkdir -p "$DESTINO"

# 2. Bucle para iterar sobre cada fichero .lean en el directorio de origen.
echo "Iniciando la copia de ficheros..."
for fichero_origen in "$ORIGEN"/*.lean; do
    # 3. Comprobar si hay ficheros que coincidan para evitar errores si no hay ninguno.
    if [ -f "$fichero_origen" ]; then
        # Extraer solo el nombre del fichero con su extensión (ej: Addition.lean)
        nombre_fichero_completo=$(basename "$fichero_origen")

        # 4. Construir el nuevo nombre del fichero de destino.
        # Aquí es donde se añade el nombre original como sufijo.
        # Por ejemplo, si el fichero es "Addition.lean", el nuevo será "Addition.lean.txt".
        nombre_fichero_destino="${nombre_fichero_completo}.txt"

        # 5. Copiar el fichero al destino con su nuevo nombre.
        cp "$fichero_origen" "$DESTINO/$nombre_fichero_destino"

        echo "Copiado: $fichero_origen  ->  $DESTINO/$nombre_fichero_destino"
    fi
done

echo "¡Proceso de copias *.lean completado con éxito"
for fichero_origen in "$ORIGEN"/*.md; do
    # 3. Comprobar si hay ficheros que coincidan para evitar errores si no hay ninguno.
    if [ -f "$fichero_origen" ]; then
        # Extraer solo el nombre del fichero con su extensión (ej: Addition.md)
        nombre_fichero_completo=$(basename "$fichero_origen")

        # 4. Construir el nuevo nombre del fichero de destino.
        # Aquí es donde se añade el nombre original como sufijo.
        # Por ejemplo, si el fichero es "Addition.md", el nuevo será "Addition.md.txt".
        nombre_fichero_destino="${nombre_fichero_completo}.txt"

        # 5. Copiar el fichero al destino con su nuevo nombre.
        cp "$fichero_origen" "$DESTINO/$nombre_fichero_destino"

        echo "Copiado: $fichero_origen  ->  $DESTINO/$nombre_fichero_destino"
    fi
done
echo "¡Proceso completado!"