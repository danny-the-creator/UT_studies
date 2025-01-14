
let tableContainerId = 'table';
let detailsContainerId = 'details';
let pokemonTypes = {};
let selectedPokemonType = {};
let basePokemonType = {
    "name": null,
    "imgUrl": null,
    "japaneseName": null,
    "pokedexNumber": null,
    "abilities": null,
    "baseAttack": null,
    "captureRate": null,
    "classification": null,
    "baseDefense": null,
    "baseHeight": null,
    "baseHp": null,
    "baseSpAttack": null,
    "baseSpDefense": null,
    "baseSpeed": null,
    "primaryType": null,
    "secondaryType": null,
    "baseWeight": null,
    "generation": null,
    "isLegendary": null
};
let defaultPokemonType = {
    "name": "Pikachu",
    "id": 513,
    "created": "24/04/2024",
    "lastUpDate": "24/04/2024",
    "imgUrl": "./images/pikachu.png",
    "japaneseName": "Pikachuピカチュウ",
    "pokedexNumber": 25,
    "abilities": ["Static", "Lightningrod"],
    "baseAttack": 55,
    "captureRate": 190,
    "classification": "Mouse Pokémon",
    "baseDefense": 40,
    "baseHeight": 0.4,
    "baseHp": 35,
    "baseSpAttack": 50,
    "baseSpDefense": 50,
    "baseSpeed": 90,
    "primaryType": "electric",
    "secondaryType": "",
    "baseWeight": 6,
    "generation": 1,
    "isLegendary": "FALSE"
}

function changeSelectedPokemonType(id) {
    selectedPokemonType = pokemonTypes?.data?.find(pt => pt.id === id);
    showDetails();
}

function showDetails() {
    const detailsContainer = document.getElementById(detailsContainerId);

    detailsContainer.innerHTML = `
    <div class="card" id="${selectedPokemonType.id}_card">
      <img src="${selectedPokemonType.imgUrl}" class="card-img-top" alt="${selectedPokemonType.classification}">
      <div class="card-body">
        <h5 class="card-title">${selectedPokemonType.name} #${selectedPokemonType.pokedexNumber}</h5>
        <p class="card-text">
            <span class="font-weight-bold">Japanese name:</span> ${selectedPokemonType.japaneseName} </br>
            <span class="font-weight-bold">Classification:</span> ${selectedPokemonType.classification} </br>
            <span class="font-weight-bold">Generation:</span> ${selectedPokemonType.generation} </br>
            <span class="font-weight-bold">Legendary:</span> ${selectedPokemonType.isLegendary ? "Yes" : "No"} </br>
            <span class="font-weight-bold">Type:</span> ${selectedPokemonType.primaryType}${selectedPokemonType.secondaryType ? " , " + selectedPokemonType.secondaryType : ""}
        </p>
      </div>
      
      <ul class="list-group list-group-flush">
            <li class="list-group-item">
                <span class="font-weight-bold">ID:</span> ${selectedPokemonType.id}
            </li>
            <li class="list-group-item">
                <span class="font-weight-bold">Created:</span> ${selectedPokemonType.created}
            </li>
            <li class="list-group-item">
                <span class="font-weight-bold">Last update:</span> ${selectedPokemonType.lastUpDate}
            </li>
            <li class="list-group-item">
                <span class="font-weight-bold">Name:</span> ${selectedPokemonType.name}
            </li>
            <li class="list-group-item">
                <span class="font-weight-bold">Pokédex number:</span> #${selectedPokemonType.pokedexNumber}
            </li>
            <li class="list-group-item">
                <span class="font-weight-bold">Japanese name:</span> ${selectedPokemonType.japaneseName}
            </li>
            <li class="list-group-item">
                <span class="font-weight-bold">Classification:</span> ${selectedPokemonType.classification}
            </li>
            <li class="list-group-item">
                <span class="font-weight-bold">Generation:</span> ${selectedPokemonType.generation}
            </li>
            <li class="list-group-item">
                <span class="font-weight-bold">Legendary:</span> ${selectedPokemonType.isLegendary ? "Yes" : "No"}
            </li>
            <li class="list-group-item">
                <span class="font-weight-bold">Image URL:</span> ${selectedPokemonType.imgUrl}
            </li>
            <li class="list-group-item">
                <span class="font-weight-bold">HP:</span> ${selectedPokemonType.baseHp}
            </li>
            <li class="list-group-item">
                <span class="font-weight-bold">Height:</span> ${selectedPokemonType.baseHeight}
            </li>
            <li class="list-group-item">
                <span class="font-weight-bold">Weight:</span> ${selectedPokemonType.baseWeight}
            </li>
            <li class="list-group-item">
                <span class="font-weight-bold">Attack:</span> ${selectedPokemonType.baseAttack}
            </li>
            <li class="list-group-item">
                <span class="font-weight-bold">Special Attack:</span> ${selectedPokemonType.baseSpAttack}
            </li>
            <li class="list-group-item">
                <span class="font-weight-bold">Defense:</span> ${selectedPokemonType.baseDefense}
            </li>
            <li class="list-group-item">
                <span class="font-weight-bold">Special Defense:</span> ${selectedPokemonType.baseSpDefense}
            </li>
            <li class="list-group-item">
                <span class="font-weight-bold">Speed:</span> ${selectedPokemonType.baseSpeed}
            </li>
            <li class="list-group-item">
                <span class="font-weight-bold">Capture rate:</span> ${selectedPokemonType.captureRate}
            </li>
            <li class="list-group-item">
                <span class="font-weight-bold">Primary type:</span> ${selectedPokemonType.primaryType}
            </li>
            <li class="list-group-item">
                <span class="font-weight-bold">Secondary type:</span> ${selectedPokemonType.secondaryType}
            </li>
            <li class="list-group-item">
                <span class="font-weight-bold">Abilities:</span> ${selectedPokemonType.abilities?.join(", ") || "none"}
            </li>
            <li class="list-group-item d-flex justify-content-between">
                <a class="btn btn-primary" onclick="showCreateForm()">New</a>
                <a class="btn btn-primary" onclick="showUpdateForm()">Update</a>
                <a class="btn btn-danger" onclick="deletePokemonType(selectedPokemonType.id)">Delete</a>
            </li>
      </ul>
    </div>
    `
}


function createPokemonTypesTable() {
    const tableContainer = document.getElementById(tableContainerId);
    tableContainer.innerHTML = `
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

    if(pokemonTypes?.data?.[0]?.id)
        changeSelectedPokemonType(pokemonTypes?.data?.[0]?.id)
}

function pokemonTypeToRow(pokemonType) {
    return `
    <tr id="${pokemonType.id}_row" onclick="changeSelectedPokemonType('${pokemonType?.id?.trim()}')">
        <th scope="row">${pokemonType.id}</th>
        <td>${pokemonType.name}</td>
        <td>#${pokemonType.pokedexNumber}</td>
        <td>${pokemonType.primaryType}</td>
        <td>${pokemonType.secondaryType || '-'}</td>
    </tr>
    `
}

function getPokemonTypes() {
    return fetch('./api/pokemonTypes')
        .then(res => res.json())
        .then(data => {
            pokemonTypes = data;
            createPokemonTypesTable();
        })
        .catch(err => {
            console.error(`Unable to fetch Pokemon Types: ${err.status}`);
            console.error(err);
        });
}

function deletePokemonType(id) {
    return fetch(`./api/pokemonTypes/${id}`, { method: "DELETE" })
        .then(() => {
            getPokemonTypes()
        })
        .catch(err => {
            console.error(`Unable to delete Pokemon Type: ${err.status}`);
            console.error(err);
        });
}


function showUpdateForm() {
    const detailsContainer = document.getElementById(detailsContainerId);

    detailsContainer.innerHTML = `
    <form id="update-form">
          <div class="form-group">
                <label for="input-name">Name</label>
                <input type="text" class="form-control" id="input-name" name="name" placeholder="${selectedPokemonType.name}">
          </div>
          <div class="form-group">
                <label for="input-classification">Classification</label>
                <input type="text" class="form-control" id="input-classification" name="classification" placeholder="${selectedPokemonType.classification}">
          </div>
          <div class="form-group">
                <label for="input-japanese-name">Japanese name</label>
                <input type="text" class="form-control" id="input-japanese-name" name="japaneseName" placeholder="${selectedPokemonType.japaneseName}">
          </div>
          <div class="form-group">
                <label for="input-img-url">Image URL</label>
                <input type="text" class="form-control" id="input-img-url" name="imgUrl" placeholder="${selectedPokemonType.imgUrl}">
          </div>
          <div class="d-flex justify-content-between">
                <button type="submit" class="btn btn-primary">Submit</button>
                <button type="button" class="btn btn-danger" onclick="showDetails()">Cancel</button>
          </div>
    </form>
    `

    const form = document.getElementById("update-form");
    form.addEventListener("submit", function(event) {
        event.preventDefault();

        let formData = new FormData(form);
        formData.forEach((v,k) => {
            selectedPokemonType[k] = formData.get(k) || selectedPokemonType[k];
        })

        const id = selectedPokemonType.id;
        fetch(`./api/pokemonTypes/${id}`, {
            method: "PUT",
            headers: { "Content-Type": "application/json" },
            body: JSON.stringify(selectedPokemonType, null, 2)
        }).then(res => getPokemonTypes())
            .then(() => changeSelectedPokemonType(id))
            .catch(err => {
                console.error("Error updating resource", err)
            })
    })
}

function showCreateForm() {
    const detailsContainer = document.getElementById(detailsContainerId);

    detailsContainer.innerHTML = `
    <form id="create-form">
          <div class="form-group">
                <label for="input-name">Name</label>
                <input type="text" class="form-control" id="input-name" name="name" placeholder="${defaultPokemonType.name}">
          </div>
          <div class="form-group">
                <label for="input-classification">Classification</label>
                <input type="text" class="form-control" id="input-classification" name="classification" placeholder="${defaultPokemonType.classification}">
          </div>
          <div class="form-group">
                <label for="input-japanese-name">Japanese name</label>
                <input type="text" class="form-control" id="input-japanese-name" name="japaneseName" placeholder="${defaultPokemonType.japaneseName}">
          </div>
          <div class="form-group">
                <label for="input-img-url">Image URL</label>
                <input type="text" class="form-control" id="input-img-url" name="imgUrl" placeholder="${defaultPokemonType.imgUrl}">
          </div>
          <div class="d-flex justify-content-between">
                <button type="submit" class="btn btn-primary">Submit</button>
                <button type="button" class="btn btn-danger" onclick="showDetails()">Cancel</button>
          </div>
    </form>
    `

    const form = document.getElementById("create-form");
    form.addEventListener("submit", function(event) {
        event.preventDefault();

        let newPokemonType = JSON.parse(JSON.stringify(basePokemonType));
        let formData = new FormData(form);
        formData.forEach((v,k) => {
            newPokemonType[k] = formData.get(k);
        })

        let newId;
        fetch(`./api/pokemonTypes`, {
            method: "POST",
            headers: { "Content-Type": "application/json" },
            body: JSON.stringify(newPokemonType, null, 2)
        }).then(res => res.json())
            .then(data => {
                newId = data.id;
                return getPokemonTypes();
            })
            .then(() => changeSelectedPokemonType(newId))
            .catch(err => {
                console.error("Error updating resource", err)
            })
    })
}
