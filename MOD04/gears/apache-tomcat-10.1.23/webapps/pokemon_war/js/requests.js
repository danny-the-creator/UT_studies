
let pokemonTypes = {};
let tableParentId = 'table';
let detailsParentId = 'details';

function getRowId(resource) {
    return `${resource.id}_row`
}

function updateDetails(pokemonTypeId) {
    const pt = pokemonTypes?.data?.find(item => item.id === pokemonTypeId);
    const parent = document.getElementById(detailsParentId);

    parent.innerHTML = `
    <div class="card" id="${pt.id}_card">
      <img src="${pt.imgUrl}" class="card-img-top" alt="${pt.classification}">
      <div class="card-body">
        <h5 class="card-title">${pt.name} #${pt.pokedexNumber}</h5>
        <p class="card-text">
            Japanese name: ${pt.japaneseName} </br>
            Classification: ${pt.classification} </br>
            Abilities: ${pt.abilities?.join(", ") || "none"} </br>
            Type: ${pt.primaryType}${pt.secondaryType ? " , " + pt.secondaryType : ""}
        </p>
      </div>
    </div>
    `
}

function pokemonTypeToRow(pokemonType) {
    return `
    <tr id="${getRowId(pokemonType)}" onclick="updateDetails('${pokemonType?.id?.trim()}')">
        <th scope="row">${pokemonType.id}</th>
        <td>${pokemonType.name}</td>
        <td>#${pokemonType.pokedexNumber}</td>
        <td>${pokemonType.primaryType}</td>
        <td>${pokemonType.secondaryType || '-'}</td>
    </tr>
    `
}

function createPokemonTypesTable() {
    const tableParent = document.getElementById(tableParentId);
    tableParent.innerHTML = `
        <table class="table table-striped table-hover">
            <thead>
                <tr>
                    <th scope="col">ID</th>
                    <th scope="col">Name</th>
                    <th scope="col">Pokedex Number</th>
                    <th scope="col">Primary Type</th>
                    <th scope="col">Secondary Type</th>
                </tr>
            </thead>
            <tbody>
                ${
                    pokemonTypes.data.map(resource => `${pokemonTypeToRow(resource)}`).join("\n")
                    || "no data"
                }
            </tbody>
        </table>
    `
}