/*
 * Copyright © 2022 Mark Raynsford <code@io7m.com> https://www.io7m.com
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
 * SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR
 * IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 */


package com.io7m.genevan.core;

import com.io7m.jaffirm.core.Invariants;
import com.io7m.jaffirm.core.Postconditions;
import com.io7m.jaffirm.core.Preconditions;
import com.io7m.junreachable.UnreachableCodeException;

import java.text.MessageFormat;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.ResourceBundle;
import java.util.Set;
import java.util.stream.Collectors;

import static com.io7m.genevan.core.GenProtocolErrorCode.AMBIGUOUS_RESULT;
import static com.io7m.genevan.core.GenProtocolErrorCode.CLIENT_AND_SERVER_HAVE_NOTHING_IN_COMMON;

/**
 * The default protocol solver.
 */

public final class GenProtocolSolver implements GenProtocolSolverType
{
  private final ResourceBundle resources;

  private GenProtocolSolver(
    final ResourceBundle inResources)
  {
    this.resources =
      Objects.requireNonNull(inResources, "resources");
  }

  /**
   * @return The default protocol solver using the system's default locale.
   */

  public static GenProtocolSolverType create()
  {
    return create(Locale.getDefault());
  }

  /**
   * @param locale The locale
   *
   * @return The default protocol solver using the given locale.
   */

  public static GenProtocolSolverType create(
    final Locale locale)
  {
    final var resources =
      ResourceBundle.getBundle(
        "com.io7m.genevan.core.Messages", locale);

    return new GenProtocolSolver(resources);
  }

  private static boolean hasCompatibleServerEndpoint(
    final Set<GenProtocolServerEndpointType> serverEndpoints,
    final GenProtocolClientHandlerType clientHandler)
  {
    return serverEndpoints.stream()
      .anyMatch(s -> s.isCompatibleWith(clientHandler));
  }

  private static boolean hasCompatibleClientHandler(
    final Set<GenProtocolClientHandlerType> clientHandlers,
    final GenProtocolServerEndpointType serverEndpoint)
  {
    return clientHandlers.stream()
      .anyMatch(s -> s.isCompatibleWith(serverEndpoint));
  }

  private static Map<String, BestVersionForProtocol> collectBestVersions(
    final Map<String, SupportedHandlersForProtocol> allProtocols)
  {
    final Map<String, BestVersionForProtocol> bestVersions = new HashMap<>();

    for (final var handlers : allProtocols.values()) {
      Preconditions.checkPrecondition(
        !bestVersions.containsKey(handlers.name),
        "Protocol names must be unique"
      );
      bestVersions.put(handlers.name, findBestVersionOf(handlers));
    }

    final var protocolNames =
      allProtocols.keySet()
        .stream()
        .collect(Collectors.toUnmodifiableSet());

    Postconditions.checkPostcondition(
      Objects.equals(bestVersions.keySet(), protocolNames),
      "Best versions must not lose protocol names."
    );
    return bestVersions;
  }

  private static BestVersionForProtocol findBestVersionOf(
    final SupportedHandlersForProtocol handlers)
  {
    final var sortedClientHandlers =
      new ArrayList<>(handlers.clientHandlers);
    final var sortedServerEndpoints =
      new ArrayList<>(handlers.serverEndpoints);

    final var clientComparator =
      Comparator.<GenProtocolClientHandlerType, GenProtocolVersion>
          comparing(o -> o.supported().version())
        .reversed();

    final var serverComparator =
      Comparator.<GenProtocolServerEndpointType, GenProtocolVersion>
          comparing(o -> o.supported().version())
        .reversed();

    sortedClientHandlers.sort(clientComparator);
    sortedServerEndpoints.sort(serverComparator);

    for (final var clientHandler : sortedClientHandlers) {
      for (final var serverHandler : sortedServerEndpoints) {
        if (clientHandler.isCompatibleWith(serverHandler)) {
          return new BestVersionForProtocol(
            handlers.name,
            serverHandler,
            clientHandler
          );
        }
      }
    }

    /*
     * The preconditions on the SupportedHandlersForProtocol constructor
     * ensure that the above loop _must_ find a result.
     */

    throw new UnreachableCodeException();
  }

  private static Map<String, SupportedHandlersForProtocol> collectSupportedProtocols(
    final Map<String, HandlersForProtocol> allProtocols)
  {
    final Map<String, SupportedHandlersForProtocol> supported = new HashMap<>();

    for (final var handlers : allProtocols.values()) {
      final var clientHandlers =
        new HashSet<>(handlers.clientHandlers);
      final var serverEndpoints =
        new HashSet<>(handlers.serverEndpoints);

      clientHandlers.removeIf(
        c -> !hasCompatibleServerEndpoint(serverEndpoints, c)
      );
      serverEndpoints.removeIf(
        s -> !hasCompatibleClientHandler(clientHandlers, s)
      );

      if (clientHandlers.isEmpty() || serverEndpoints.isEmpty()) {
        continue;
      }

      supported.put(
        handlers.name,
        new SupportedHandlersForProtocol(
          handlers.name, serverEndpoints, clientHandlers)
      );
    }

    return supported;
  }

  private static Map<String, HandlersForProtocol> collectProtocols(
    final Map<String, ServerEndpointsByName> serverEndpointsByName,
    final Map<String, ClientHandlersByName> clientHandlersByName)
  {
    final var collected = new HashMap<String, HandlersForProtocol>();

    for (final var serverEndpoints : serverEndpointsByName.values()) {
      final var protocolName = serverEndpoints.name;

      final var clientHandlers =
        clientHandlersByName.getOrDefault(
          protocolName,
          new ClientHandlersByName(protocolName, new HashSet<>())
        );

      final var handlers =
        collected.getOrDefault(
          protocolName,
          new HandlersForProtocol(
            protocolName,
            new HashSet<>(),
            new HashSet<>())
        );

      handlers.serverEndpoints.addAll(serverEndpoints.serverEndpoints);
      handlers.clientHandlers.addAll(clientHandlers.clientHandlers);
      collected.put(protocolName, handlers);
    }

    for (final var clientHandlers : clientHandlersByName.values()) {
      final var protocolName = clientHandlers.name;

      final var serverEndpoints =
        serverEndpointsByName.getOrDefault(
          protocolName,
          new ServerEndpointsByName(protocolName, new HashSet<>())
        );

      final var handlers =
        collected.getOrDefault(
          protocolName,
          new HandlersForProtocol(
            protocolName,
            new HashSet<>(),
            new HashSet<>())
        );

      handlers.serverEndpoints.addAll(serverEndpoints.serverEndpoints);
      handlers.clientHandlers.addAll(clientHandlers.clientHandlers);
      collected.put(protocolName, handlers);
    }

    Invariants.checkInvariant(
      collected.keySet().containsAll(clientHandlersByName.keySet()),
      "Protocol set must contain all protocols supported by client handlers."
    );
    Invariants.checkInvariant(
      collected.keySet().containsAll(serverEndpointsByName.keySet()),
      "Protocol set must contain all protocols supported by server endpoints."
    );
    return collected;
  }

  private static Map<String, ClientHandlersByName> collectClientHandlers(
    final Collection<? extends GenProtocolClientHandlerType> clientSupports)
  {
    final var collected = new HashMap<String, ClientHandlersByName>();

    for (final var clientHandler : clientSupports) {
      final var supported =
        clientHandler.supported();
      final var identifier =
        supported.identifier();
      final var existing =
        collected.getOrDefault(
          identifier, new ClientHandlersByName(identifier, new HashSet<>())
        );

      existing.clientHandlers.add(clientHandler);
      collected.put(identifier, existing);
    }

    final var clientProvidesNames =
      clientSupports.stream()
        .map(e -> e.supported().identifier())
        .collect(Collectors.toUnmodifiableSet());

    Postconditions.checkPostcondition(
      Objects.equals(collected.keySet(), clientProvidesNames),
      "Collected client handlers must not lose protocol names."
    );
    return collected;
  }

  private static Map<String, ServerEndpointsByName> collectServerEndpoints(
    final Collection<? extends GenProtocolServerEndpointType> serverProvides)
  {
    final var collected = new HashMap<String, ServerEndpointsByName>();

    for (final var serverEndpoint : serverProvides) {
      final var supported =
        serverEndpoint.supported();
      final var identifier =
        supported.identifier();
      final var existing =
        collected.getOrDefault(
          identifier, new ServerEndpointsByName(identifier, new HashSet<>())
        );

      existing.serverEndpoints.add(serverEndpoint);
      collected.put(identifier, existing);
    }

    final var serverProvidesNames =
      serverProvides.stream()
        .map(e -> e.supported().identifier())
        .collect(Collectors.toUnmodifiableSet());

    Postconditions.checkPostcondition(
      Objects.equals(collected.keySet(), serverProvidesNames),
      "Collected server endpoints must not lose protocol names."
    );
    return collected;
  }

  private static Optional<BestVersionForProtocol> disambiguate(
    final Map<String, BestVersionForProtocol> bestVersions,
    final List<String> preferProtocols)
  {
    for (final var protocol : preferProtocols) {
      final var bestVersion =
        bestVersions.get(protocol);
      if (bestVersion != null) {
        return Optional.of(bestVersion);
      }
    }
    return Optional.empty();
  }

  @Override
  public GenProtocolSolved solve(
    final Collection<? extends GenProtocolServerEndpointType> serverProvides,
    final Collection<? extends GenProtocolClientHandlerType> clientSupports,
    final List<String> preferProtocols)
    throws GenProtocolException
  {
    Objects.requireNonNull(serverProvides, "serverProvides");
    Objects.requireNonNull(clientSupports, "clientSupports");
    Objects.requireNonNull(preferProtocols, "preferProtocols");

    if (serverProvides.isEmpty()) {
      throw new GenProtocolException(
        CLIENT_AND_SERVER_HAVE_NOTHING_IN_COMMON,
        this.format("errorServerSupportsNothing")
      );
    }

    if (clientSupports.isEmpty()) {
      throw new GenProtocolException(
        CLIENT_AND_SERVER_HAVE_NOTHING_IN_COMMON,
        this.format("errorClientSupportsNothing")
      );
    }

    final Map<String, ServerEndpointsByName> serverEndpointsByName =
      collectServerEndpoints(serverProvides);
    final Map<String, ClientHandlersByName> clientHandlersByName =
      collectClientHandlers(clientSupports);

    final Map<String, HandlersForProtocol> allProtocols =
      collectProtocols(serverEndpointsByName, clientHandlersByName);
    final Map<String, SupportedHandlersForProtocol> supportedProtocols =
      collectSupportedProtocols(allProtocols);

    if (supportedProtocols.isEmpty()) {
      throw this.errorNoProtocolsInCommon(serverProvides, clientSupports);
    }

    final Map<String, BestVersionForProtocol> bestVersions =
      collectBestVersions(supportedProtocols);

    if (bestVersions.size() == 1) {
      final var version =
        bestVersions.values()
          .iterator()
          .next();

      return new GenProtocolSolved(
        version.clientHandler,
        version.serverEndpoint
      );
    }

    final Optional<BestVersionForProtocol> disambiguated =
      disambiguate(bestVersions, preferProtocols);

    if (disambiguated.isPresent()) {
      return new GenProtocolSolved(
        disambiguated.get().clientHandler(),
        disambiguated.get().serverEndpoint()
      );
    }

    throw this.errorAmbiguous(
      serverProvides,
      clientSupports,
      preferProtocols
    );
  }

  private String format(
    final String id,
    final Object... args)
  {
    return MessageFormat.format(this.resources.getString(id), args);
  }

  private GenProtocolException errorNoProtocolsInCommon(
    final Collection<? extends GenProtocolServerEndpointType> serverProvides,
    final Collection<? extends GenProtocolClientHandlerType> clientSupports)
  {
    final var lineSeparator = System.lineSeparator();
    final var text = new StringBuilder(128);
    text.append(this.format("errorNoSupportedVersions"));
    text.append(lineSeparator);
    text.append(lineSeparator);

    text.append(this.format("serverSupports"));
    text.append(lineSeparator);

    for (final var candidate : serverProvides) {
      final var supported = candidate.supported();
      text.append("    ");
      text.append(supported.identifier());
      text.append(" ");
      text.append(supported.version().versionMajor());
      text.append(".");
      text.append(supported.version().versionMinor());
      text.append(lineSeparator);
    }
    text.append(lineSeparator);

    text.append(this.format("clientSupports"));
    text.append(lineSeparator);

    for (final var handler : clientSupports) {
      final var supported = handler.supported();
      text.append("    ");
      text.append(supported.identifier());
      text.append(" ");
      text.append(supported.version().versionMajor());
      text.append(".");
      text.append(supported.version().versionMinor());
      text.append(lineSeparator);
    }

    return new GenProtocolException(
      CLIENT_AND_SERVER_HAVE_NOTHING_IN_COMMON,
      text.toString()
    );
  }

  private GenProtocolException errorAmbiguous(
    final Collection<? extends GenProtocolServerEndpointType> serverProvides,
    final Collection<? extends GenProtocolClientHandlerType> clientSupports,
    final List<String> preferProtocols)
  {
    final var lineSeparator = System.lineSeparator();
    final var text = new StringBuilder(128);
    text.append(this.format("errorAmbiguousProtocols"));
    text.append(lineSeparator);
    text.append(lineSeparator);

    text.append(this.format("serverSupports"));
    text.append(lineSeparator);

    for (final var candidate : serverProvides) {
      final var supported = candidate.supported();
      text.append("    ");
      text.append(supported.identifier());
      text.append(" ");
      text.append(supported.version().versionMajor());
      text.append(".");
      text.append(supported.version().versionMinor());
      text.append(lineSeparator);
    }
    text.append(lineSeparator);

    text.append(this.format("clientSupports"));
    text.append(lineSeparator);

    for (final var handler : clientSupports) {
      final var supported = handler.supported();
      text.append("    ");
      text.append(supported.identifier());
      text.append(" ");
      text.append(supported.version().versionMajor());
      text.append(".");
      text.append(supported.version().versionMinor());
      text.append(lineSeparator);
    }
    text.append(lineSeparator);

    if (!preferProtocols.isEmpty()) {
      text.append(this.format("clientPrefers", preferProtocols));
      text.append(lineSeparator);
    } else {
      text.append(this.format("clientPrefersNone"));
      text.append(lineSeparator);
    }

    text.append(lineSeparator);
    text.append(this.format(
      "clientPreferSuggest",
      serverProvides.stream()
        .map(GenProtocolServerEndpointType::supported)
        .map(GenProtocolIdentifier::identifier)
        .toList()
    ));

    return new GenProtocolException(
      AMBIGUOUS_RESULT,
      text.toString()
    );
  }

  private record ServerEndpointsByName(
    String name,
    Set<GenProtocolServerEndpointType> serverEndpoints)
  {
    private ServerEndpointsByName
    {
      Objects.requireNonNull(name, "name");
      Objects.requireNonNull(serverEndpoints, "serverEndpoints");
    }
  }

  private record ClientHandlersByName(
    String name,
    Set<GenProtocolClientHandlerType> clientHandlers)
  {
    private ClientHandlersByName
    {
      Objects.requireNonNull(name, "name");
      Objects.requireNonNull(clientHandlers, "clientHandlers");
    }
  }

  private record HandlersForProtocol(
    String name,
    Set<GenProtocolServerEndpointType> serverEndpoints,
    Set<GenProtocolClientHandlerType> clientHandlers)
  {
    private HandlersForProtocol
    {
      Objects.requireNonNull(name, "name");
      Objects.requireNonNull(serverEndpoints, "serverEndpoints");
      Objects.requireNonNull(clientHandlers, "clientHandlers");
    }
  }

  private record SupportedHandlersForProtocol(
    String name,
    Set<GenProtocolServerEndpointType> serverEndpoints,
    Set<GenProtocolClientHandlerType> clientHandlers)
  {
    private SupportedHandlersForProtocol
    {
      Objects.requireNonNull(name, "name");
      Objects.requireNonNull(serverEndpoints, "serverEndpoints");
      Objects.requireNonNull(clientHandlers, "clientHandlers");

      Preconditions.checkPrecondition(
        !serverEndpoints.isEmpty(),
        "Server endpoints cannot be empty"
      );
      Preconditions.checkPrecondition(
        !clientHandlers.isEmpty(),
        "Client handlers cannot be empty"
      );

      for (final var s : serverEndpoints) {
        Preconditions.checkPrecondition(
          hasCompatibleClientHandler(clientHandlers, s),
          "All server endpoints must have a supported client handler."
        );
      }
      for (final var c : clientHandlers) {
        Preconditions.checkPrecondition(
          hasCompatibleServerEndpoint(serverEndpoints, c),
          "All client handlers must have a supported server endpoint."
        );
      }
    }
  }

  private record BestVersionForProtocol(
    String name,
    GenProtocolServerEndpointType serverEndpoint,
    GenProtocolClientHandlerType clientHandler)
  {
    private BestVersionForProtocol
    {
      Objects.requireNonNull(name, "name");
      Objects.requireNonNull(serverEndpoint, "serverEndpoint");
      Objects.requireNonNull(clientHandler, "clientHandler");

      Preconditions.checkPrecondition(
        serverEndpoint.isCompatibleWith(clientHandler),
        "Server endpoint must be compatible with client handler."
      );
      Preconditions.checkPrecondition(
        clientHandler.isCompatibleWith(serverEndpoint),
        "Client handler must be compatible with server endpoint."
      );
    }
  }
}
